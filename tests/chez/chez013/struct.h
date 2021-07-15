#pragma once

typedef struct {
    int x;
    int y;
} point;

typedef struct {
    char *name;
    point *pt;
} namedpoint;

point *mkPoint(int x, int y);
void freePoint(point *pt);

namedpoint *mkNamedPoint(char *str, point *p);
void freeNamedPoint(namedpoint *np);

char *getString(void *p);
