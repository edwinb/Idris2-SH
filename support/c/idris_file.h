#pragma once

#include <stdint.h>
#include <stdio.h>

FILE *idris2_openFile(char *name, char *mode);
void idris2_closeFile(FILE *f);

int idris2_fileError(FILE *f);

// Turn errno into an integer understandable by System.File
int idris2_fileErrno();

int idris2_removeFile(const char *filename);
int idris2_fileSize(FILE *h);

int idris2_fpoll(FILE *f);

// Seek through the next newline without
// saving anything along the way
int idris2_seekLine(FILE *f);

// Treat as a Ptr String (might be NULL)
char *idris2_readLine(FILE *f);
char *idris2_readChars(int num, FILE *f);
size_t idris2_readBufferData(FILE *h, char *buffer, size_t loc, size_t max);

int idris2_writeLine(FILE *f, char *str);
size_t idris2_writeBufferData(FILE *h, const char *buffer, size_t loc,
                              size_t len);

int idris2_eof(FILE *f);
int idris2_fileAccessTime(FILE *f);
int idris2_fileModifiedTime(FILE *f);
int idris2_fileStatusTime(FILE *f);

FILE *idris2_stdin();
FILE *idris2_stdout();
FILE *idris2_stderr();
