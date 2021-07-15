#include "conCaseHelper.h"

AConAlt *newConstructorField(int nr) {
    AConAlt *retVal = (AConAlt *)malloc(nr * sizeof(AConAlt));
    for (int i = 0; i < nr; i++) {
        retVal[i].tag = -1;
    }
    return retVal;
}

void freeConstructorField(AConAlt *cf) {
    free(cf);
}

void constructorFieldFNextEntry(AConAlt *field, char *name, int tag) {
    AConAlt *nextEntry = field;
    while (nextEntry->tag == -1) {
        nextEntry++;
    }
    nextEntry->name = name;
    nextEntry->tag = tag;
}

int compareConstructors(Value *sc, AConAlt *field, int nr) {
    Value_Constructor *constr = (Value_Constructor *)sc;
    for (int i = 0; i < nr; i++) {
        if (field->name) // decide my name
        {
            if (!strcmp(field->name, constr->name)) {
                return i;
            }
        } else // decide by tag
        {
            if (field->tag == constr->tag) {
                return i;
            }
        }
        field++;
    }
    return -1;
}

int multiStringCompare(Value *sc, int nrDecicionOptions, char **options) {
    for (int i = 0; i < nrDecicionOptions; i++) {
        if (!strcmp(((Value_String *)sc)->str, options[i])) {
            return i;
        }
    }
    return -1;
}

int multiDoubleCompare(Value *sc, int nrDecicionOptions, double *options) {
    for (int i = 0; i < nrDecicionOptions; i++) {
        if (((Value_Double *)sc)->d == options[i]) {
            return i;
        }
    }
    return -1;
}
