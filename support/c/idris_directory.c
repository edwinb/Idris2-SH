#include "idris_directory.h"

#include <dirent.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

char *idris2_currentDirectory() {
    char *cwd = malloc(1024); // probably ought to deal with the unlikely event
                              // of this being too small
    return getcwd(cwd, 1024); // Freed by RTS
}

int idris2_changeDir(char *dir) {
    return chdir(dir);
}

int idris2_createDir(char *dir) {
#ifdef _WIN32
    return mkdir(dir);
#else
    return mkdir(dir, S_IRWXU | S_IRWXG | S_IRWXO);
#endif
}

typedef struct {
    DIR *dirptr;
    int error;
} DirInfo;

void *idris2_openDir(char *dir) {
    DIR *d = opendir(dir);
    if (d == NULL) {
        return NULL;
    } else {
        DirInfo *di = malloc(sizeof(DirInfo));
        di->dirptr = d;
        di->error = 0;

        return (void *)di;
    }
}

void idris2_closeDir(void *d) {
    DirInfo *di = (DirInfo *)d;

    closedir(di->dirptr);
    free(di);
}

int idris2_removeDir(char *path) {
    return rmdir(path);
}

char *idris2_nextDirEntry(void *d) {
    DirInfo *di = (DirInfo *)d;
    struct dirent *de = readdir(di->dirptr);

    if (de == NULL) {
        di->error = -1;
        return NULL;
    } else {
        return de->d_name;
    }
}
