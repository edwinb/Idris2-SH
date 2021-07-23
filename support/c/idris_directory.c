#include "idris_directory.h"

#include <dirent.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include "idris_util.h"

char* idris2_currentDirectory() {
   char* cwd = malloc(1024); // probably ought to deal with the unlikely event of this being too small
   IDRIS2_VERIFY(cwd, "malloc failed");
   return getcwd(cwd, 1024); // Freed by RTS
}

int idris2_changeDir(char* dir) {
    return chdir(dir);
}

int idris2_createDir(char* dir) {
#ifdef _WIN32
    return mkdir(dir);
#else
    return mkdir(dir, S_IRWXU | S_IRWXG | S_IRWXO);
#endif
}

typedef struct {
    DIR* dirptr;
} DirInfo;

void* idris2_openDir(char* dir) {
    DIR *d = opendir(dir);
    if (d == NULL) {
        return NULL;
    } else {
        DirInfo* di = malloc(sizeof(DirInfo));
        IDRIS2_VERIFY(di, "malloc failed");
        di->dirptr = d;

        return (void*)di;
    }
}

void idris2_closeDir(void* d) {
    DirInfo* di = (DirInfo*)d;

    IDRIS2_VERIFY(closedir(di->dirptr) == 0, "closedir failed: %s", strerror(errno));
    free(di);
}

int idris2_removeDir(char* path) {
    return rmdir(path);
}

char* idris2_nextDirEntry(void* d) {
    DirInfo* di = (DirInfo*)d;
    // `readdir` keeps `errno` unchanged on end of stream
    // so we need to reset `errno` to distinguish between
    // end of stream and failure.
    errno = 0;
    struct dirent* de = readdir(di->dirptr);

    if (de == NULL) {
        return NULL;
    } else {
        return de->d_name;
    }
}
