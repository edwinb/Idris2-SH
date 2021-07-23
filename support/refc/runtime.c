#include "runtime.h"
#include "refc_util.h"

#ifdef INTEGER_USE_LIBBF
extern void init_bf();
#endif

void init_idris2() {
#ifdef INTEGER_USE_LIBBF
  init_bf();
#endif
}

void missing_ffi()
{
  fprintf(
    stderr,
    "Foreign function declared, but not defined.\n"
    "Cannot call missing FFI - aborting.\n"
  );
  exit(1);
}

void push_Arglist(Value_Arglist *arglist, Value *arg)
{
  IDRIS2_REFC_VERIFY(arglist->filled < arglist->total, "unable to add more arguments to arglist");

  arglist->args[arglist->filled] = newReference(arg);
  arglist->filled++;
}

Value *apply_closure(Value *_clos, Value *arg)
{
  // create a new arg list
  Value_Arglist *oldArgs = ((Value_Closure *)_clos)->arglist;
  Value_Arglist *newArgs = newArglist(0, oldArgs->total);
  newArgs->filled = oldArgs->filled + 1;
  // add argument to new arglist
  for (int i = 0; i < oldArgs->filled; i++)
  {
    newArgs->args[i] = newReference(oldArgs->args[i]);
  }
  newArgs->args[oldArgs->filled] = newReference(arg);

  Value_Closure *clos = (Value_Closure *)_clos;

  // check if enough arguments exist
  if (newArgs->filled >= newArgs->total)
  {
    fun_ptr_t f = clos->f;
    while (1)
    {
      Value *retVal = f(newArgs);
      removeReference((Value *)newArgs);
      if (!retVal || retVal->header.tag != COMPLETE_CLOSURE_TAG)
      {
        return retVal;
      }
      f = ((Value_Closure *)retVal)->f;
      newArgs = ((Value_Closure *)retVal)->arglist;
      newArgs = (Value_Arglist *)newReference((Value *)newArgs);
      removeReference(retVal);
    }
  }

  return (Value *)makeClosureFromArglist(clos->f, newArgs);
}

Value *tailcall_apply_closure(Value *_clos, Value *arg)
{
  // create a new arg list
  Value_Arglist *oldArgs = ((Value_Closure *)_clos)->arglist;
  Value_Arglist *newArgs = newArglist(0, oldArgs->total);
  newArgs->filled = oldArgs->filled + 1;
  // add argument to new arglist
  for (int i = 0; i < oldArgs->filled; i++)
  {
    newArgs->args[i] = newReference(oldArgs->args[i]);
  }
  newArgs->args[oldArgs->filled] = newReference(arg);

  Value_Closure *clos = (Value_Closure *)_clos;

  // check if enough arguments exist
  if (newArgs->filled >= newArgs->total)
    return (Value *)makeClosureFromArglist(clos->f, newArgs);

  return (Value *)makeClosureFromArglist(clos->f, newArgs);
}

int extractInt(Value *v)
{
  if (v->header.tag == INTEGER_TAG)
  {
#ifdef INTEGER_USE_LIBBF
    int64_t res;
    bf_get_int64(&res, &((Value_Integer*)v)->i, 0);
    return (int)res;
#else
    return (int)mpz_get_si(((Value_Integer *)v)->i);
#endif
  }

  if (v->header.tag == INT8_TAG)
  {
    return (int)((Value_Int8 *)v)->i8;
  }

  if (v->header.tag == INT16_TAG)
  {
    return (int)((Value_Int16 *)v)->i16;
  }

  if (v->header.tag == INT32_TAG)
  {
    return (int)((Value_Int32 *)v)->i32;
  }

  if (v->header.tag == INT64_TAG)
  {
    return (int)((Value_Int64 *)v)->i64;
  }

  if (v->header.tag == DOUBLE_TAG)
  {
    return (int)((Value_Double *)v)->d;
  }

  if (v->header.tag == CHAR_TAG)
  {
    return (int)((Value_Char *)v)->c;
  }

  return -1;
}

Value *trampoline(Value *closure)
{
  fun_ptr_t f = ((Value_Closure *)closure)->f;
  Value_Arglist *_arglist = ((Value_Closure *)closure)->arglist;
  Value_Arglist *arglist = (Value_Arglist *)newReference((Value *)_arglist);
  removeReference(closure);
  while (1)
  {
    Value *retVal = f(arglist);
    removeReference((Value *)arglist);
    if (!retVal || retVal->header.tag != COMPLETE_CLOSURE_TAG)
    {
      return retVal;
    }
    f = ((Value_Closure *)retVal)->f;
    arglist = ((Value_Closure *)retVal)->arglist;
    arglist = (Value_Arglist *)newReference((Value *)arglist);
    removeReference(retVal);
  }
  return NULL;
}
