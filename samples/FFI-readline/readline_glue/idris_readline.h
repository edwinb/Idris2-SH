#pragma once

void idrisrl_setCompletion(rl_completion_func_t *fn);

char *getString(void *str);
void *mkString(char *str);
void *nullString();
int isNullString(void *str);
