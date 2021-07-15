// To compile this file for the samples `sample/ffi/Small.dir` and
// `sample/ffi/Struct.idr`, you will need to manually compile and link it into a
// `.so` file, and place it in a location where the resulting exectuable can
// find it. For example:
//      gcc -c -fPIC smallc.c -o smallc.o
//      gcc smallc.o -shared -o libsmallc.so
//      idris2 Small.idr
// For an example of using Idris packages to build external (FFI) libraries, see
// the `FFI-readline` sample, and specifically `readline.ipkg`

#include <stdio.h>
#include <stdlib.h>

int add(int x, int y) {
    return x + y;
}

int addWithMessage(char *msg, int x, int y) {
    printf("%s: %d + %d = %d\n", msg, x, y, x + y);
    return x + y;
}

typedef char *(*StringFn)(char *, int);

char *applyFn(char *x, int y, StringFn f) {
    printf("Applying callback to %s %d\n", x, y);
    return f(x, y);
}

char *applyFnPure(char *x, int y, StringFn f) {
    return f(x, y);
}

typedef struct {
    int x;
    int y;
} point;

point *mkPoint(int x, int y) {
    point *pt = malloc(sizeof(point));
    pt->x = x;
    pt->y = y;
    return pt;
}

void freePoint(point *pt) {
    free(pt);
}
