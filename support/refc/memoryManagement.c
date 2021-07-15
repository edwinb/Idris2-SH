#include "runtime.h"

Value *newValue() {
    Value *retVal = (Value *)malloc(sizeof(Value));
    retVal->header.refCounter = 1;
    retVal->header.tag = NO_TAG;
    return retVal;
}

Value_Arglist *newArglist(int missing, int total) {
    Value_Arglist *retVal = (Value_Arglist *)newValue();
    retVal->header.tag = ARGLIST_TAG;
    retVal->total = total;
    retVal->filled = total - missing;
    retVal->args = (Value **)malloc(sizeof(Value *) * total);
    memset(retVal->args, 0, sizeof(Value *) * total);
    return retVal;
}

Value_Constructor *newConstructor(int total, int tag, const char *name) {
    Value_Constructor *retVal = (Value_Constructor *)newValue();
    retVal->header.tag = CONSTRUCTOR_TAG;
    retVal->total = total;
    retVal->tag = tag;
    int nameLength = strlen(name);
    retVal->name = malloc(nameLength + 1);
    memset(retVal->name, 0, nameLength + 1);
    memcpy(retVal->name, name, nameLength);
    retVal->args = (Value **)malloc(sizeof(Value *) * total);
    return retVal;
}

Value_Closure *makeClosureFromArglist(fun_ptr_t f, Value_Arglist *arglist) {
    Value_Closure *retVal = (Value_Closure *)newValue();
    retVal->header.tag = CLOSURE_TAG;
    retVal->arglist =
        arglist; // (Value_Arglist *)newReference((Value*)arglist);
    retVal->f = f;
    if (retVal->arglist->filled >= retVal->arglist->total) {
        retVal->header.tag = COMPLETE_CLOSURE_TAG;
    }
    return retVal;
}

Value_Double *makeDouble(double d) {
    Value_Double *retVal = (Value_Double *)newValue();
    retVal->header.tag = DOUBLE_TAG;
    retVal->d = d;
    return retVal;
}

Value_Char *makeChar(char c) {
    Value_Char *retVal = (Value_Char *)newValue();
    retVal->header.tag = CHAR_TAG;
    retVal->c = c;
    return retVal;
}

Value_Bits8 *makeBits8(uint8_t i) {
    Value_Bits8 *retVal = (Value_Bits8 *)newValue();
    retVal->header.tag = BITS8_TAG;
    retVal->ui8 = i;
    return retVal;
}

Value_Bits16 *makeBits16(uint16_t i) {
    Value_Bits16 *retVal = (Value_Bits16 *)newValue();
    retVal->header.tag = BITS16_TAG;
    retVal->ui16 = i;
    return retVal;
}

Value_Bits32 *makeBits32(uint32_t i) {
    Value_Bits32 *retVal = (Value_Bits32 *)newValue();
    retVal->header.tag = BITS32_TAG;
    retVal->ui32 = i;
    return retVal;
}

Value_Bits64 *makeBits64(uint64_t i) {
    Value_Bits64 *retVal = (Value_Bits64 *)newValue();
    retVal->header.tag = BITS64_TAG;
    retVal->ui64 = i;
    return retVal;
}

Value_Int8 *makeInt8(int8_t i) {
    Value_Int8 *retVal = (Value_Int8 *)newValue();
    retVal->header.tag = INT8_TAG;
    retVal->i8 = i;
    return retVal;
}

Value_Int16 *makeInt16(int16_t i) {
    Value_Int16 *retVal = (Value_Int16 *)newValue();
    retVal->header.tag = INT16_TAG;
    retVal->i16 = i;
    return retVal;
}

Value_Int32 *makeInt32(int32_t i) {
    Value_Int32 *retVal = (Value_Int32 *)newValue();
    retVal->header.tag = INT32_TAG;
    retVal->i32 = i;
    return retVal;
}

Value_Int64 *makeInt64(int64_t i) {
    Value_Int64 *retVal = (Value_Int64 *)newValue();
    retVal->header.tag = INT64_TAG;
    retVal->i64 = i;
    return retVal;
}

Value_Int8 *makeBool(int p) {
    return makeInt8(p ? 1 : 0);
}

Value_Integer *makeInteger() {
    Value_Integer *retVal = (Value_Integer *)newValue();
    retVal->header.tag = INTEGER_TAG;
    mpz_init(retVal->i);
    return retVal;
}

Value_Integer *makeIntegerLiteral(char *i) {
    Value_Integer *retVal = makeInteger();
    mpz_set_str(retVal->i, i, 10);
    return retVal;
}

Value_String *makeEmptyString(size_t l) {
    Value_String *retVal = (Value_String *)newValue();
    retVal->header.tag = STRING_TAG;
    retVal->str = malloc(l);
    memset(retVal->str, 0, l);
    return retVal;
}

Value_String *makeString(char *s) {
    Value_String *retVal = (Value_String *)newValue();
    int l = strlen(s);
    retVal->header.tag = STRING_TAG;
    retVal->str = malloc(l + 1);
    memset(retVal->str, 0, l + 1);
    memcpy(retVal->str, s, l);
    return retVal;
}

Value_Pointer *makePointer(void *ptr_Raw) {
    Value_Pointer *p = (Value_Pointer *)newValue();
    p->header.tag = POINTER_TAG;
    p->p = ptr_Raw;
    return p;
}

Value_GCPointer *makeGCPointer(void *ptr_Raw, Value_Closure *onCollectFct) {
    Value_GCPointer *p = (Value_GCPointer *)newValue();
    p->header.tag = GC_POINTER_TAG;
    p->p = makePointer(ptr_Raw);
    p->onCollectFct = onCollectFct;
    return p;
}

Value_Buffer *makeBuffer(void *buf) {
    Value_Buffer *b = (Value_Buffer *)newValue();
    b->header.tag = BUFFER_TAG;
    b->buffer = buf;
    return b;
}

Value_Array *makeArray(int length) {
    Value_Array *a = (Value_Array *)newValue();
    a->header.tag = ARRAY_TAG;
    a->capacity = length;
    a->arr = (Value **)malloc(sizeof(Value *) * length);
    memset(a->arr, 0, sizeof(Value *) * length);
    return a;
}

Value_World *makeWorld() {
    Value_World *retVal = (Value_World *)newValue();
    retVal->header.tag = WORLD_TAG;
    retVal->listIORefs = NULL;
    return retVal;
}

Value *newReference(Value *source) {
    // note that we explicitly allow NULL as source (for erased arguments)
    if (source) {
        source->header.refCounter++;
    }
    return source;
}

void removeReference(Value *elem) {
    if (!elem) {
        return;
    }
    // remove reference counter
    elem->header.refCounter--;
    if (elem->header.refCounter == 0)
    // recursively remove all references to all children
    {
        switch (elem->header.tag) {
        case BITS8_TAG:
        case BITS16_TAG:
        case BITS32_TAG:
        case BITS64_TAG:
        case INT8_TAG:
        case INT16_TAG:
        case INT32_TAG:
        case INT64_TAG:
            /* nothing to delete, added for sake of completeness */
            break;
        case INTEGER_TAG: {
            mpz_clear(((Value_Integer *)elem)->i);
            break;
        }
        case DOUBLE_TAG:
            /* nothing to delete, added for sake of completeness */
            break;
        case CHAR_TAG:
            /* nothing to delete, added for sake of completeness */
            break;
        case STRING_TAG:
            free(((Value_String *)elem)->str);
            break;

        case CLOSURE_TAG: {
            Value_Closure *cl = (Value_Closure *)elem;
            Value_Arglist *al = cl->arglist;
            removeReference((Value *)al);
            break;
        }
        case COMPLETE_CLOSURE_TAG: {
            Value_Closure *cl = (Value_Closure *)elem;
            Value_Arglist *al = cl->arglist;
            removeReference((Value *)al);
            break;
        }
        case ARGLIST_TAG: {
            Value_Arglist *al = (Value_Arglist *)elem;
            for (int i = 0; i < al->filled; i++) {
                removeReference(al->args[i]);
            }
            free(al->args);
            break;
        }
        case CONSTRUCTOR_TAG: {
            Value_Constructor *constr = (Value_Constructor *)elem;
            for (int i = 0; i < constr->total; i++) {
                removeReference(constr->args[i]);
            }
            if (constr->name) {
                free(constr->name);
            }
            free(constr->args);
            break;
        }
        case IOREF_TAG:
            /* nothing to delete, added for sake of completeness */
            break;

        case BUFFER_TAG: {
            Value_Buffer *b = (Value_Buffer *)elem;
            free(b->buffer);
            break;
        }

        case ARRAY_TAG: {
            Value_Array *a = (Value_Array *)elem;
            for (int i = 0; i < a->capacity; i++) {
                removeReference(a->arr[i]);
            }
            free(a->arr);
            break;
        }
        case POINTER_TAG:
            /* nothing to delete, added for sake of completeness */
            break;

        case GC_POINTER_TAG: {
            /* maybe here we need to invoke onCollectAny */
            Value_GCPointer *vPtr = (Value_GCPointer *)elem;
            Value *closure1 =
                apply_closure((Value *)vPtr->onCollectFct, (Value *)vPtr->p);
            apply_closure(closure1, NULL);
            removeReference(closure1);
            removeReference((Value *)vPtr->onCollectFct);
            removeReference((Value *)vPtr->p);
            break;
        }
        case WORLD_TAG: {
            Value_World *w = (Value_World *)elem;
            if (w->listIORefs) {
                for (int i = 0; i < w->listIORefs->filled; i++) {
                    removeReference(w->listIORefs->refs[i]);
                }
                free(w->listIORefs->refs);
                free(w->listIORefs);
            }
        }
        default:
            break;
        }
        // finally, free element
        free(elem);
    }
}
