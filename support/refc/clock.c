#include "clock.h"

#define NSEC_PER_SEC 1000000000
#define CLOCKS_PER_NSEC ((float)CLOCKS_PER_SEC / NSEC_PER_SEC)

Value *clockTimeMonotonic() {
    return clockTimeUtc();
}

Value *clockTimeUtc() {
    return (Value *)makeBits64(time(NULL) * NSEC_PER_SEC);
}

Value *clockTimeProcess() {
    uint64_t time_ns = clock() / CLOCKS_PER_NSEC;
    return (Value *)makeBits64(time_ns);
}

Value *clockTimeThread() {
    return clockTimeProcess();
}

Value *clockTimeGcCpu() {
    return NULL;
}

Value *clockTimeGcReal() {
    return NULL;
}

int clockValid(Value *clock) {
    return clock != NULL;
}

uint64_t clockSecond(Value *clock) {
    uint64_t totalNano = ((Value_Bits64 *)clock)->ui64;
    return totalNano / NSEC_PER_SEC;
}

uint64_t clockNanosecond(Value *clock) {
    uint64_t totalNano = ((Value_Bits64 *)clock)->ui64;
    return totalNano % NSEC_PER_SEC;
}
