#pragma once

#include "cBackend.h"

void init_idris2();
void missing_ffi();

Value *apply_closure(Value *, Value *arg);
void push_Arglist(Value_Arglist *arglist, Value *arg);

int extractInt(Value *);
Value *trampoline(Value *closure);
Value *tailcall_apply_closure(Value *_clos, Value *arg);
