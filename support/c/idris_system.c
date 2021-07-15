#include "idris_system.h"
#include <stdlib.h>

int idris2_system(const char *command) {
    return system(command);
}
