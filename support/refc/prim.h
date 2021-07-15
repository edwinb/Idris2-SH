#pragma once

#include "cBackend.h"

// IORef

Value *newIORef(Value *, Value *, Value *);
Value *readIORef(Value *, Value *, Value *);
Value *writeIORef(Value *, Value *, Value *, Value *);

// Sys

Value *sysOS(void);
Value *idris2_crash(Value *msg);

// Array

Value *newArray(Value *, Value *, Value *, Value *);
Value *arrayGet(Value *, Value *, Value *, Value *);
Value *arraySet(Value *, Value *, Value *, Value *, Value *);

// Pointer
Value *onCollect(Value *, Value *, Value *, Value *);
Value *onCollectAny(Value *, Value *, Value *, Value *);

Value *voidElim(Value *, Value *);

// Threads
Value *System_Concurrency_Raw_prim__mutexRelease(Value *, Value *);

Value *System_Concurrency_Raw_prim__mutexAcquire(Value *, Value *);

Value *System_Concurrency_Raw_prim__makeMutex(Value *);

Value *System_Concurrency_Raw_prim__makeCondition(Value *);

Value *System_Concurrency_Raw_prim__conditionWait(Value *, Value *, Value *);

Value *System_Concurrency_Raw_prim__conditionWaitTimeout(Value *, Value *,
                                                         Value *, Value *);

Value *System_Concurrency_Raw_prim__conditionSignal(Value *, Value *);

Value *System_Concurrency_Raw_prim__conditionBroadcast(Value *, Value *);
