#pragma once

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void *newBuffer(int bytes);

int getBufferSize(void *buffer);

void setBufferByte(void *buffer, int loc, int byte);
void setBufferInt(void *buffer, int loc, int64_t val);
void setBufferDouble(void *buffer, int loc, double val);
void setBufferString(void *buffer, int loc, char *str);
size_t writeBufferData(FILE *h, void *buffer, size_t loc, size_t len);

void copyBuffer(void *from, int start, int len, void *to, int loc);

uint8_t getBufferByte(void *buffer, int loc);
int64_t getBufferInt(void *buffer, int loc);
double getBufferDouble(void *buffer, int loc);
char *getBufferString(void *buffer, int loc, int len);
size_t readBufferData(FILE *h, void *buffer, size_t loc, size_t max);
