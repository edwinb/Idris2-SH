#include "prim.h"
#include <unistd.h>

// This is NOT THREAD SAFE in the current implementation

IORef_Storage *newIORef_Storage(int capacity) {
    IORef_Storage *retVal = (IORef_Storage *)malloc(sizeof(IORef_Storage));
    retVal->filled = 0;
    retVal->total = capacity;
    retVal->refs = (Value **)malloc(sizeof(Value *) * retVal->total);
    return retVal;
}

void doubleIORef_Storage(IORef_Storage *ior) {
    Value **values = (Value **)malloc(sizeof(Value *) * ior->total * 2);
    ior->total *= 2;
    for (int i = 0; i < ior->filled; i++) {
        values[i] = ior->refs[i];
    }
    free(ior->refs);
    ior->refs = values;
}

Value *newIORef(Value *erased, Value *input_value, Value *_world) {
    // if no ioRef Storag exist, start with one
    Value_World *world = (Value_World *)_world;
    if (!world->listIORefs) {
        world->listIORefs = newIORef_Storage(128);
    }
    // expand size of needed
    if (world->listIORefs->filled >= world->listIORefs->total) {
        doubleIORef_Storage(world->listIORefs);
    }

    // store value
    Value_IORef *ioRef = (Value_IORef *)newValue();
    ioRef->header.tag = IOREF_TAG;
    ioRef->index = world->listIORefs->filled;
    world->listIORefs->refs[world->listIORefs->filled] =
        newReference(input_value);
    world->listIORefs->filled++;

    return (Value *)ioRef;
}

Value *readIORef(Value *erased, Value *_index, Value *_world) {
    Value_World *world = (Value_World *)_world;
    Value_IORef *index = (Value_IORef *)_index;
    return newReference(world->listIORefs->refs[index->index]);
}

Value *writeIORef(Value *erased, Value *_index, Value *new_value,
                  Value *_world) {
    Value_World *world = (Value_World *)_world;
    Value_IORef *index = (Value_IORef *)_index;
    removeReference(world->listIORefs->refs[index->index]);
    world->listIORefs->refs[index->index] = newReference(new_value);
    return newReference(_index);
}

// -----------------------------------
//       System operations
// -----------------------------------

Value *sysOS(void) {
#ifdef _WIN32
    return (Value *)makeString("windows");
#elif _WIN64
    return (Value *)makeString("windows");
#elif __APPLE__ || __MACH__
    return (Value *)makeString("macOS");
#elif __linux__
    return (Value *)makeString("Linux");
#elif __FreeBSD__
    return (Value *)makeString("FreeBSD");
#elif __OpenBSD__
    return (Value *)makeString("OpenBSD");
#elif __NetBSD__
    return (Value *)makeString("NetBSD");
#elif __DragonFly__
    return (Value *)makeString("DragonFly");
#elif __unix || __unix__
    return (Value *)makeString("Unix");
#else
    return (Value *)makeString("Other");
#endif
}

Value *idris2_crash(Value *msg) {
    Value_String *str = (Value_String *)msg;
    printf("ERROR: %s\n", str->str);
    exit(-1);
}

//
//
//
// // -----------------------------------
// //         Array operations
// // -----------------------------------

Value *newArray(Value *erased, Value *_length, Value *v, Value *_word) {
    int length = extractInt(_length);
    Value_Array *a = makeArray(length);

    for (int i = 0; i < length; i++) {
        a->arr[i] = newReference(v);
    }

    return (Value *)a;
}

Value *arrayGet(Value *erased, Value *_array, Value *_index, Value *_word) {
    Value_Array *a = (Value_Array *)_array;
    return newReference(a->arr[((Value_Int64 *)_index)->i64]);
}

Value *arraySet(Value *erased, Value *_array, Value *_index, Value *v,
                Value *_word) {
    Value_Array *a = (Value_Array *)_array;
    removeReference(a->arr[((Value_Int64 *)_index)->i64]);
    a->arr[((Value_Int64 *)_index)->i64] = newReference(v);
    return NULL;
}

//
// -----------------------------------
//      Pointer operations
// -----------------------------------

Value *onCollect(Value *_erased, Value *_anyPtr, Value *_freeingFunction,
                 Value *_world) {
    printf("onCollect called\n");
    Value_GCPointer *retVal = (Value_GCPointer *)newValue();
    retVal->header.tag = GC_POINTER_TAG;
    retVal->p = (Value_Pointer *)newReference(_anyPtr);
    retVal->onCollectFct = (Value_Closure *)newReference(_freeingFunction);
    return (Value *)retVal;
}

Value *onCollectAny(Value *_erased, Value *_anyPtr, Value *_freeingFunction,
                    Value *_world) {
    printf("onCollectAny called\n");
    Value_GCPointer *retVal = (Value_GCPointer *)newValue();
    retVal->header.tag = GC_POINTER_TAG;
    retVal->p = (Value_Pointer *)_anyPtr;
    retVal->onCollectFct = (Value_Closure *)_freeingFunction;
    return (Value *)retVal;
}

Value *voidElim(Value *erased1, Value *erased2) {
    return NULL;
}

// Threads

// %foreign "scheme:blodwen-mutex"
// prim__makeMutex : PrimIO Mutex
// using pthread_mutex_init(pthread_mutex_t *mutex, const pthread_mutexattr_t
// *attr)
Value *System_Concurrency_Raw_prim__makeMutex(Value *_world) {
    Value_Mutex *mut = (Value_Mutex *)newValue();
    mut->header.tag = MUTEX_TAG;
    mut->mutex = (pthread_mutex_t *)malloc(sizeof(pthread_mutex_t));
    if (pthread_mutex_init(mut->mutex, NULL)) {
        fprintf(stderr, "Error init Mutex\n");
        exit(-1);
    }
    return (Value *)mut;
}

// %foreign "scheme:blodwen-lock"
// prim__mutexAcquire : Mutex -> PrimIO ()
// using pthread_mutex_lock(pthread_mutex_t *mutex)
Value *System_Concurrency_Raw_prim__mutexAcquire(Value *_mutex, Value *_world) {
    if (pthread_mutex_lock(((Value_Mutex *)_mutex)->mutex)) {
        fprintf(stderr, "Error locking mutex\n");
        exit(-1);
    }
    return NULL;
}

// %foreign "scheme:blodwen-unlock"
// prim__mutexRelease : Mutex -> PrimIO ()
// using int pthread_mutex_unlock(pthread_mutex_t *mutex)
Value *System_Concurrency_Raw_prim__mutexRelease(Value *_mutex, Value *_world) {
    if (pthread_mutex_unlock(((Value_Mutex *)_mutex)->mutex)) {
        fprintf(stderr, "Error locking mutex\n");
        exit(-1);
    }
    return NULL;
}

// %foreign "scheme:blodwen-condition"
// prim__makeCondition : PrimIO Condition
// using int pthread_cond_init(pthread_cond_t *cond, const pthread_condattr_t
// *attr) with standard initialisation
Value *System_Concurrency_Raw_prim__makeCondition(Value *_world) {
    // typedef struct{
    //     Value_header header;
    //     pthread_cond_t *cond;
    // }Value_Condition;

    Value_Condition *c = (Value_Condition *)newValue();
    c->header.tag = CONDITION_TAG;
    c->cond = (pthread_cond_t *)malloc(sizeof(pthread_cond_t));
    if (pthread_cond_init(c->cond, NULL)) {
        fprintf(stderr, "error init condition\n");
        exit(-1);
    }
    return (Value *)c;
}

// %foreign "scheme:blodwen-condition-wait"
// prim__conditionWait : Condition -> Mutex -> PrimIO ()
// using int pthread_cond_wait(pthread_cond_t *, pthread_mutex_t *mutex)
Value *System_Concurrency_Raw_prim__conditionWait(Value *_condition,
                                                  Value *_mutex,
                                                  Value *_world) {
    Value_Condition *cond = (Value_Condition *)_condition;
    Value_Mutex *mutex = (Value_Mutex *)_mutex;
    if (pthread_cond_wait(cond->cond, mutex->mutex)) {
        fprintf(stderr, "Error Conditional Wait\n");
        exit(-1);
    }
    return NULL;
}

// %foreign "scheme:blodwen-condition-wait-timeout"
// prim__conditionWaitTimeout : Condition -> Mutex -> Int -> PrimIO ()
// using int pthread_cond_timedwait(pthread_cond_t *cond, pthread_mutex_t
// *mutex, const struct timespec *abstime)
Value *System_Concurrency_Raw_prim__conditionWaitTimeout(Value *_condition,
                                                         Value *_mutex,
                                                         Value *_timeout,
                                                         Value *_world) {
    Value_Condition *cond = (Value_Condition *)_condition;
    Value_Mutex *mutex = (Value_Mutex *)_mutex;
    Value_Int64 *timeout = (Value_Int64 *)_timeout;
    struct timespec t;
    t.tv_sec = timeout->i64 / 1000000;
    t.tv_nsec = timeout->i64 % 1000000;
    if (pthread_cond_timedwait(cond->cond, mutex->mutex, &t)) {
        fprintf(stderr, "Error in pthread_cond_timedwait\n");
        exit(-1);
    }
    return NULL;
}

// %foreign "scheme:blodwen-condition-signal"
// prim__conditionSignal : Condition -> PrimIO ()
// using int pthread_cond_signal(pthread_cond_t *cond)
Value *System_Concurrency_Raw_prim__conditionSignal(Value *_condition,
                                                    Value *_world) {
    Value_Condition *cond = (Value_Condition *)_condition;
    if (pthread_cond_signal(cond->cond)) {
        fprintf(stderr, "Error in pthread_cond_signal\n");
        exit(-1);
    }
    return NULL;
}

// %foreign "scheme:blodwen-condition-broadcast"
// prim__conditionBroadcast : Condition -> PrimIO ()
// using int pthread_cond_broadcast(pthread_cond_t *cond)
Value *System_Concurrency_Raw_prim__conditionBroadcast(Value *_condition,
                                                       Value *_mutex) {
    Value_Condition *cond = (Value_Condition *)_condition;
    if (pthread_cond_broadcast(cond->cond)) {
        fprintf(stderr, "Error in pthread_cond_broadcast\n");
        exit(-1);
    }
    return NULL;
}
