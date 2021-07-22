#include "idris_memory.h"

#include <errno.h>
#include <stdlib.h>
#include <string.h>

#include "idris_util.h"

void* idris2_malloc(int size) {
    IDRIS2_VERIFY(size >= 0, "malloc negative argument: %d", size);

    if (size == 0) {
        // Do not depend on platform-speific behavior of malloc.
        return NULL;
    }

    void* ptr = malloc(size);
    IDRIS2_VERIFY(ptr, "malloc failed: %s", strerror(errno));
    return ptr;
}

void idris2_free(void* ptr) {
    if (!ptr) {
        return;
    }
    free(ptr);
}

// TODO: remove `idrnet_malloc` and `idrnet_free` after bootstrap update

void* idrnet_malloc(int size) {
    return idris2_malloc(size);
}

void idrnet_free(void* ptr) {
    idris2_free(ptr);
}

char* idris2_strdup(const char* s) {
    char* r = strdup(s);
    IDRIS2_VERIFY(r, "strdup failed");
    return r;
}
