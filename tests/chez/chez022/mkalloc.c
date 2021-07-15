#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    int val;
    char *str;
} Stuff;

Stuff *mkThing() {
    static int num = 0;
    Stuff *x = malloc(sizeof(Stuff));
    x->val = num++;
    x->str = malloc(20);
    strcpy(x->str, "Hello");
    return x;
}

char *getStr(Stuff *x) {
    return x->str;
}

void freeThing(Stuff *x) {
    printf("Freeing %d %s\n", x->val, x->str);
    free(x->str);
    free(x);
}
