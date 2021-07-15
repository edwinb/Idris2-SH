#include "stringOps.h"

Value *stringLength(Value *s) {
    int length = strlen(((Value_String *)s)->str);
    return (Value *)makeInt64(length);
}

Value *head(Value *str) {
    Value_Char *c = (Value_Char *)newValue();
    c->header.tag = CHAR_TAG;
    c->c = ((Value_String *)str)->str[0];
    return (Value *)c;
}

Value *tail(Value *input) {
    Value_String *tailStr = (Value_String *)newValue();
    tailStr->header.tag = STRING_TAG;
    Value_String *s = (Value_String *)input;
    int l = strlen(s->str);
    if (l != 0) {
        tailStr->str = malloc(l);
        memset(tailStr->str, 0, l);
        memcpy(tailStr->str, s->str + 1, l - 1);
        return (Value *)tailStr;
    } else {
        tailStr->str = malloc(1);
        tailStr->str[0] = '\0';
        return (Value *)tailStr;
    }
}

Value *reverse(Value *str) {
    Value_String *retVal = (Value_String *)newValue();
    retVal->header.tag = STRING_TAG;
    Value_String *input = (Value_String *)str;
    int l = strlen(input->str);
    retVal->str = malloc(l + 1);
    memset(retVal->str, 0, l + 1);
    char *p = retVal->str;
    char *q = input->str + (l - 1);
    for (int i = 0; i < l; i++) {
        *p++ = *q--;
    }
    return (Value *)retVal;
}

Value *strIndex(Value *str, Value *i) {
    char *s = ((Value_String *)str)->str;
    int idx = ((Value_Int64 *)i)->i64;
    return (Value *)makeChar(s[idx]);
}

Value *strCons(Value *c, Value *str) {
    int l = strlen(((Value_String *)str)->str);
    Value_String *retVal = makeEmptyString(l + 2);
    retVal->str[0] = ((Value_Char *)c)->c;
    memcpy(retVal->str + 1, ((Value_String *)str)->str, l);
    return (Value *)retVal;
}

Value *strAppend(Value *a, Value *b) {
    int la = strlen(((Value_String *)a)->str);
    int lb = strlen(((Value_String *)b)->str);
    Value_String *retVal = makeEmptyString(la + lb + 1);
    memcpy(retVal->str, ((Value_String *)a)->str, la);
    memcpy(retVal->str + la, ((Value_String *)b)->str, lb);
    return (Value *)retVal;
}

Value *strSubstr(Value *start, Value *len, Value *s) {
    char *input = ((Value_String *)s)->str;
    int offset = extractInt(start);
    int l = extractInt(len);

    int tailLen = strlen(input);
    if (tailLen < l) {
        l = tailLen;
    }

    Value_String *retVal = makeEmptyString(l + 1);
    memcpy(retVal->str, input + offset, l);

    return (Value *)retVal;
}

char *fastPack(Value *charList) {
    Value_Constructor *current;

    int l = 0;
    current = (Value_Constructor *)charList;
    while (current->total == 2) {
        l++;
        current = (Value_Constructor *)current->args[1];
    }

    char *retVal = malloc(l + 1);
    retVal[l] = 0;

    int i = 0;
    current = (Value_Constructor *)charList;
    while (current->total == 2) {
        retVal[i++] = ((Value_Char *)current->args[0])->c;
        current = (Value_Constructor *)current->args[1];
    }

    return retVal;
}

Value *fastUnpack(char *str) {
    if (str[0] == '\0') {
        return (Value *)newConstructor(0, 0, "Prelude_Types_Nil");
    }

    Value_Constructor *retVal =
        newConstructor(2, 1, "Prelude_Types__colon_colon");
    retVal->args[0] = (Value *)makeChar(str[0]);

    int i = 1;
    Value_Constructor *current = retVal;
    Value_Constructor *next;
    while (str[i] != '\0') {
        next = newConstructor(2, 1, "Prelude_Types__colon_colon");
        next->args[0] = (Value *)makeChar(str[i]);
        current->args[1] = (Value *)next;

        i++;
        current = next;
    }
    current->args[1] = (Value *)newConstructor(0, 0, "Prelude_Types_Nil");

    return (Value *)retVal;
}

char *fastConcat(Value *strList) {
    Value_Constructor *current;

    int totalLength = 0;
    current = (Value_Constructor *)strList;
    while (current->total == 2) {
        totalLength += strlen(((Value_String *)current->args[0])->str);
        current = (Value_Constructor *)current->args[1];
    }

    char *retVal = malloc(totalLength + 1);
    retVal[totalLength] = '\0';

    char *currentStr;
    int currentStrLen;
    int offset = 0;
    current = (Value_Constructor *)strList;
    while (current->total == 2) {
        currentStr = ((Value_String *)current->args[0])->str;
        currentStrLen = strlen(currentStr);
        memcpy(retVal + offset, currentStr, currentStrLen);

        offset += currentStrLen;
        current = (Value_Constructor *)current->args[1];
    }

    return retVal;
}

typedef struct {
    char *str;
    int pos;
} String_Iterator;

Value *stringIteratorNew(char *str) {
    int l = strlen(str);

    String_Iterator *it = (String_Iterator *)malloc(sizeof(String_Iterator));
    it->str = (char *)malloc(l + 1);
    it->pos = 0;
    memcpy(it->str, str, l + 1); // Take a copy of str, in case it gets GCed

    Value_Arglist *arglist = newArglist(2, 2);
    Value *(*onCollectRaw)(Value_Arglist *) = onCollectStringIterator_arglist;
    Value_Closure *onCollect = makeClosureFromArglist(onCollectRaw, arglist);

    return (Value *)makeGCPointer(it, onCollect);
}

Value *onCollectStringIterator(Value_Pointer *ptr, void *null) {
    String_Iterator *it = (String_Iterator *)ptr->p;
    free(it->str);
    free(it);
    return NULL;
}

Value *onCollectStringIterator_arglist(Value_Arglist *arglist) {
    return onCollectStringIterator((Value_Pointer *)arglist->args[0],
                                   arglist->args[1]);
}

Value *stringIteratorToString(void *a, char *str, Value *it_p,
                              Value_Closure *f) {
    String_Iterator *it = ((Value_GCPointer *)it_p)->p->p;
    return apply_closure((Value *)f, (Value *)makeString(it->str + it->pos));
}

Value *stringIteratorNext(char *s, Value *it_p) {
    String_Iterator *it = (String_Iterator *)((Value_GCPointer *)it_p)->p->p;
    char c = it->str[it->pos];

    if (c == '\0') {
        return (Value *)newConstructor(0, 0, "Data_String_Iterator_EOF");
    }

    it->pos++; // Ok to do this as StringIterator linear

    Value_Constructor *retVal =
        newConstructor(2, 1, "Data_String_Iterator_Character");
    retVal->args[0] = (Value *)makeChar(c);
    retVal->args[1] = newReference(it_p);

    return (Value *)retVal;
}
