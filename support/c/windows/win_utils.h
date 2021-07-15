#include <stdint.h>
#include <stdio.h>

#pragma once

int win_fpoll(FILE *h);
FILE *win32_u8fopen(const char *path, const char *mode);
FILE *win32_u8popen(const char *path, const char *mode);
void win32_gettime(int64_t *sec, int64_t *nsec);
void win32_sleep(int ms);
int win32_modenv(const char *name, const char *value, int overwrite);

int win32_getErrno();
int win32_getPID();
long win32_getNProcessors();
