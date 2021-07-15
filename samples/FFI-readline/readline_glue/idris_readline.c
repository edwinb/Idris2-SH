#include <readline/readline.h>
#include <stdlib.h>
#include <string.h>

rl_compentry_func_t *my_compentry;

char *compentry_wrapper(const char *text, int i) {
    char *res = my_compentry(text, i); // Idris frees this
    if (res != NULL) {
        char *comp = malloc(strlen(res) + 1); // Readline frees this
        strcpy(comp, res);
        return comp;
    } else {
        return NULL;
    }
}

void idrisrl_setCompletion(rl_compentry_func_t *fn) {
    rl_completion_entry_function = compentry_wrapper;
    my_compentry = fn;
}

char *getString(void *str) {
    return (char *)str;
}

void *mkString(char *str) {
    return (void *)str;
}

void *nullString() {
    return NULL;
}

int isNullString(void *str) {
    return str == NULL;
}
