#pragma once

#include <time.h>

#include "cBackend.h"
#include "datatypes.h"

Value *clockTimeMonotonic();
Value *clockTimeUtc();
Value *clockTimeProcess();
Value *clockTimeThread();
Value *clockTimeGcCpu();
Value *clockTimeGcReal();

int clockValid(Value *clock);
uint64_t clockSecond(Value *clock);
uint64_t clockNanosecond(Value *clock);
