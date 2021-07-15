#pragma once

#include "cBackend.h"

typedef struct {
    char *name;
    int tag;
} AConAlt;

AConAlt *newConstructorField(int);
int compareConstructors(Value *, AConAlt *, int);
void constructorFieldFNextEntry(AConAlt *, char *, int);
void freeConstructorField(AConAlt *);

int multiStringCompare(Value *, int, char **);
int multiDoubleCompare(Value *, int, double *);
