#include "idris_file.h"
#include "getline.h"

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

#ifdef _WIN32
#include "windows/win_utils.h"
#else
#include <sys/select.h>
#endif

FILE *idris2_openFile(char *name, char *mode) {
#ifdef _WIN32
    FILE *f = win32_u8fopen(name, mode);
#else
    FILE *f = fopen(name, mode);
#endif
    return (void *)f;
}

void idris2_closeFile(FILE *f) {
    fclose(f);
}

int idris2_fileError(FILE *f) {
    return ferror(f);
}

int idris2_fileErrno() {
    switch (errno) {
    case ENOENT:
        return 2;
    case EACCES:
        return 3;
    case EEXIST:
        return 4;
    default:
        return (errno + 5);
    }
}

int idris2_removeFile(const char *filename) {
    return remove(filename);
}

int idris2_fileSize(FILE *f) {
    int fd = fileno(f);

    struct stat buf;
    if (fstat(fd, &buf) == 0) {
        return (int)(buf.st_size);
    } else {
        return -1;
    }
}

int idris2_fpoll(FILE *f) {
#ifdef _WIN32
    return win_fpoll(f);
#else
    fd_set x;
    struct timeval timeout;
    timeout.tv_sec = 1;
    timeout.tv_usec = 0;
    int fd = fileno(f);

    FD_ZERO(&x);
    FD_SET(fd, &x);

    int r = select(fd + 1, &x, 0, 0, &timeout);
    return r;
#endif
}

void *idris2_popen(const char *cmd, const char *mode) {
#ifdef _WIN32
    FILE *f = win32_u8popen(cmd, mode);
#else
    FILE *f = popen(cmd, mode);
#endif
    return f;
}

void idris2_pclose(void *stream) {
#ifdef _WIN32
    _pclose(stream);
#else
    pclose(stream);
#endif
}

// seek through the next newline, consuming and
// throwing away anything until then.
int idris2_seekLine(FILE *f) {
    while (1) {
        int c = fgetc(f);
        if (c == -1) {
            if (feof(f)) {
                return 0;
            } else {
                return -1;
            }
        }
        if (c == '\n') {
            return 0;
        }
    }
}

char *idris2_readLine(FILE *f) {
    char *buffer = NULL;
    size_t n = 0;
    ssize_t len;
    len = getline(&buffer, &n, f);
    if (len < 0 && buffer != NULL) {
        buffer[0] =
            '\0'; // Copy Idris 1 behaviour - empty string if nothing read
    }
    return buffer; // freed by RTS if not NULL
}

char *idris2_readChars(int num, FILE *f) {
    char *buffer = malloc((num + 1) * sizeof(char));
    size_t len;
    len = fread(buffer, sizeof(char), (size_t)num, f);
    buffer[len] = '\0';

    if (len <= 0) {
        return NULL;
    } else {
        return buffer; // freed by RTS
    }
}

size_t idris2_readBufferData(FILE *h, char *buffer, size_t loc, size_t max) {
    return fread(buffer + loc, sizeof(uint8_t), max, h);
}

int idris2_writeLine(FILE *f, char *str) {
    if (fputs(str, f) == EOF) {
        return 0;
    } else {
        return 1;
    }
}

size_t idris2_writeBufferData(FILE *h, const char *buffer, size_t loc,
                              size_t len) {
    return fwrite(buffer + loc, sizeof(uint8_t), len, h);
}

int idris2_eof(FILE *f) {
    return feof(f);
}

int idris2_fileAccessTime(FILE *f) {
    int fd = fileno(f);

    struct stat buf;
    if (fstat(fd, &buf) == 0) {
        return buf.st_atime;
    } else {
        return -1;
    }
}

int idris2_fileModifiedTime(FILE *f) {
    int fd = fileno(f);

    struct stat buf;
    if (fstat(fd, &buf) == 0) {
        return buf.st_mtime;
    } else {
        return -1;
    }
}

int idris2_fileStatusTime(FILE *f) {
    int fd = fileno(f);

    struct stat buf;
    if (fstat(fd, &buf) == 0) {
        return buf.st_ctime;
    } else {
        return -1;
    }
}

FILE *idris2_stdin() {
    return stdin;
}

FILE *idris2_stdout() {
    return stdout;
}

FILE *idris2_stderr() {
    return stderr;
}
