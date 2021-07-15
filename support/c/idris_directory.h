#pragma once

char *idris2_currentDirectory();
int idris2_changeDir(char *dir);
int idris2_createDir(char *dir);
void *idris2_openDir(char *dir);
void idris2_closeDir(void *d);
int idris2_removeDir(char *path);
char *idris2_nextDirEntry(void *d);
