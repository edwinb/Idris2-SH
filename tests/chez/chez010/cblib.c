#include <stdio.h>

typedef int (*IntFn)(int, int);
typedef char (*CharFn)(char, int);

int add(int x, int y) {
    return x + y;
}

int applyIntFn(int x, int y, IntFn f) {
    printf("Callback coming\n");
    fflush(stdout);
    return f(x, y);
}

int applyIntFnPure(int x, int y, IntFn f) {
    return f(x, y);
}

char applyCharFn(char c, int x, CharFn f) {
    return f(c, x);
}
