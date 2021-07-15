#include "idris_memory.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void *idris2_malloc(int size) {
    if (size < 0) {
        fprintf(stderr, "malloc negative argument: %d\n", size);
        abort();
    }

    if (size == 0) {
        // Do not depend on platform-speific behavior of malloc.
        return NULL;
    }

    void *ptr = malloc(size);
    if (!ptr) {
        fprintf(stderr, "malloc failed: %s\n", strerror(errno));
        abort();
    }
    return ptr;
}

void idris2_free(void *ptr) {
    if (!ptr) {
        return;
    }
    free(ptr);
}

// TODO: remove `idrnet_malloc` and `idrnet_free` after bootstrap update

void *idrnet_malloc(int size) {
    return idris2_malloc(size);
}

void idrnet_free(void *ptr) {
    idris2_free(ptr);
}
