#pragma once

#include "cBackend.h"

Value *stringLength(Value *);
Value *head(Value *str);
Value *tail(Value *str);
Value *reverse(Value *str);
Value *strIndex(Value *str, Value *i);
Value *strCons(Value *c, Value *str);
Value *strAppend(Value *a, Value *b);
Value *strSubstr(Value *s, Value *start, Value *len);
char *fastPack(Value *charList);
Value *fastUnpack(char *str);
char *fastConcat(Value *strList);

Value *stringIteratorNew(char *str);
Value *onCollectStringIterator(Value_Pointer *ptr, void *null);
Value *onCollectStringIterator_arglist(Value_Arglist *arglist);
Value *stringIteratorToString(void *a, char *str, Value *it_p,
                              Value_Closure *f);
Value *stringIteratorNext(char *s, Value *it_p);
