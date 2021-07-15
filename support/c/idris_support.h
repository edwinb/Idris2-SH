#pragma once

// Return non-zero if the pointer is null
int idris2_isNull(void *);
// Returns a NULL
void *idris2_getNull();
// Convert a Ptr String intro a String, assuming the string has been checked
// to be non-null
char *idris2_getString(void *p);
int idris2_getErrno();
char *idris2_strerror(int errnum);

char *idris2_getStr();
void idris2_putStr(char *f);

void idris2_sleep(int sec);
void idris2_usleep(int usec);
int idris2_time();

int idris2_getArgCount();
void idris2_setArgs(int argc, char *argv[]);
char *idris2_getArg(int n);
char *idris2_getEnvPair(int i);

int idris2_getPID();

long idris2_getNProcessors();
