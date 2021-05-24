#ifndef __MEMORY_MANAGEMENT_H__
#define __MEMORY_MANAGEMENT_H__
#include "cBackend.h"

Value *newValue(void);
Value *newReference(Value *source);
void removeReference(Value *source);

Value_Arglist *newArglist(int missing, int total);
Value_Constructor *newConstructor(int total, int tag, const char *name);

// copies arglist, no pointer bending
Value_Closure *makeClosureFromArglist(fun_ptr_t f, Value_Arglist *);

Value_Double *makeDouble(double d);
Value_Char *makeChar(char d);
Value_Bits8 *makeBits8(uint8_t i);
Value_Bits16 *makeBits16(uint16_t i);
Value_Bits32 *makeBits32(uint32_t i);
Value_Bits64 *makeBits64(uint64_t i);
Value_Int *makeInt(int64_t i);
Value_Int *makeBool(int p);
Value_Integer *makeInteger();
Value_Integer *makeIntegerLiteral(char *i);
Value_String *makeEmptyString(size_t l);
Value_String *makeString(char *);

Value_Pointer *makePointer(void *);
Value_GCPointer *makeGCPointer(void *ptr_Raw, Value_Closure *onCollectFct);
Value_Buffer *makeBuffer(void *buf);
Value_Array *makeArray(int length);
Value_World *makeWorld(void);

#endif
