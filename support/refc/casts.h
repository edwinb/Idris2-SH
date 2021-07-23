#pragma once

#include "cBackend.h"
#include <stdio.h>

Value *cast_Int8_to_Bits8(Value *);
Value *cast_Int8_to_Bits16(Value *);
Value *cast_Int8_to_Bits32(Value *);
Value *cast_Int8_to_Bits64(Value *);
Value *cast_Int8_to_Int16(Value *);
Value *cast_Int8_to_Int32(Value *);
Value *cast_Int8_to_Int64(Value *);
Value *cast_Int8_to_Integer(Value *);
Value *cast_Int8_to_double(Value *);
Value *cast_Int8_to_char(Value *);
Value *cast_Int8_to_string(Value *);

Value *cast_Int16_to_Bits8(Value *);
Value *cast_Int16_to_Bits16(Value *);
Value *cast_Int16_to_Bits32(Value *);
Value *cast_Int16_to_Bits64(Value *);
Value *cast_Int16_to_Int8(Value *);
Value *cast_Int16_to_Int32(Value *);
Value *cast_Int16_to_Int64(Value *);
Value *cast_Int16_to_Integer(Value *);
Value *cast_Int16_to_double(Value *);
Value *cast_Int16_to_char(Value *);
Value *cast_Int16_to_string(Value *);

Value *cast_Int32_to_Bits8(Value *);
Value *cast_Int32_to_Bits16(Value *);
Value *cast_Int32_to_Bits32(Value *);
Value *cast_Int32_to_Bits64(Value *);
Value *cast_Int32_to_Int8(Value *);
Value *cast_Int32_to_Int16(Value *);
Value *cast_Int32_to_Int64(Value *);
Value *cast_Int32_to_Integer(Value *);
Value *cast_Int32_to_double(Value *);
Value *cast_Int32_to_char(Value *);
Value *cast_Int32_to_string(Value *);

Value *cast_Int64_to_Bits8(Value *);
Value *cast_Int64_to_Bits16(Value *);
Value *cast_Int64_to_Bits32(Value *);
Value *cast_Int64_to_Bits64(Value *);
Value *cast_Int64_to_Int8(Value *);
Value *cast_Int64_to_Int16(Value *);
Value *cast_Int64_to_Int32(Value *);
Value *cast_Int64_to_Int64(Value *);
Value *cast_Int64_to_Integer(Value *);
Value *cast_Int64_to_double(Value *);
Value *cast_Int64_to_char(Value *);
Value *cast_Int64_to_string(Value *);

Value *cast_double_to_Bits8(Value *);
Value *cast_double_to_Bits16(Value *);
Value *cast_double_to_Bits32(Value *);
Value *cast_double_to_Bits64(Value *);
Value *cast_double_to_Int8(Value *);
Value *cast_double_to_Int16(Value *);
Value *cast_double_to_Int32(Value *);
Value *cast_double_to_Int64(Value *);
Value *cast_double_to_Integer(Value *);
Value *cast_double_to_char(Value *);
Value *cast_double_to_string(Value *);

Value *cast_char_to_Bits8(Value *);
Value *cast_char_to_Bits16(Value *);
Value *cast_char_to_Bits32(Value *);
Value *cast_char_to_Bits64(Value *);
Value *cast_char_to_Int8(Value *);
Value *cast_char_to_Int16(Value *);
Value *cast_char_to_Int32(Value *);
Value *cast_char_to_Int64(Value *);
Value *cast_char_to_Integer(Value *);
Value *cast_char_to_double(Value *);
Value *cast_char_to_string(Value *);

Value *cast_string_to_Bits8(Value *);
Value *cast_string_to_Bits16(Value *);
Value *cast_string_to_Bits32(Value *);
Value *cast_string_to_Bits64(Value *);
Value *cast_string_to_Int8(Value *);
Value *cast_string_to_Int16(Value *);
Value *cast_string_to_Int32(Value *);
Value *cast_string_to_Int64(Value *);
Value *cast_string_to_Integer(Value *);
Value *cast_string_to_double(Value *);
Value *cast_string_to_char(Value *);

Value *cast_Bits8_to_Bits16(Value *input);
Value *cast_Bits8_to_Bits32(Value *input);
Value *cast_Bits8_to_Bits64(Value *input);
Value *cast_Bits8_to_Int8(Value *input);
Value *cast_Bits8_to_Int16(Value *input);
Value *cast_Bits8_to_Int32(Value *input);
Value *cast_Bits8_to_Int64(Value *input);
Value *cast_Bits8_to_Integer(Value *input);
Value *cast_Bits8_to_double(Value *input);
Value *cast_Bits8_to_char(Value *input);
Value *cast_Bits8_to_string(Value *input);

Value *cast_Bits16_to_Bits8(Value *input);
Value *cast_Bits16_to_Bits32(Value *input);
Value *cast_Bits16_to_Bits64(Value *input);
Value *cast_Bits16_to_Int8(Value *input);
Value *cast_Bits16_to_Int16(Value *input);
Value *cast_Bits16_to_Int32(Value *input);
Value *cast_Bits16_to_Int64(Value *input);
Value *cast_Bits16_to_Integer(Value *input);
Value *cast_Bits16_to_double(Value *input);
Value *cast_Bits16_to_char(Value *input);
Value *cast_Bits16_to_string(Value *input);

Value *cast_Bits32_to_Bits8(Value *input);
Value *cast_Bits32_to_Bits16(Value *input);
Value *cast_Bits32_to_Bits64(Value *input);
Value *cast_Bits32_to_Int8(Value *input);
Value *cast_Bits32_to_Int16(Value *input);
Value *cast_Bits32_to_Int32(Value *input);
Value *cast_Bits32_to_Int64(Value *input);
Value *cast_Bits32_to_Integer(Value *input);
Value *cast_Bits32_to_double(Value *input);
Value *cast_Bits32_to_char(Value *input);
Value *cast_Bits32_to_string(Value *input);

Value *cast_Bits64_to_Bits8(Value *input);
Value *cast_Bits64_to_Bits16(Value *input);
Value *cast_Bits64_to_Bits32(Value *input);
Value *cast_Bits64_to_Int8(Value *input);
Value *cast_Bits64_to_Int16(Value *input);
Value *cast_Bits64_to_Int32(Value *input);
Value *cast_Bits64_to_Int64(Value *input);
Value *cast_Bits64_to_Integer(Value *input);
Value *cast_Bits64_to_double(Value *input);
Value *cast_Bits64_to_char(Value *input);
Value *cast_Bits64_to_string(Value *input);

Value *cast_Integer_to_Bits8(Value *input);
Value *cast_Integer_to_Bits16(Value *input);
Value *cast_Integer_to_Bits32(Value *input);
Value *cast_Integer_to_Bits64(Value *input);
Value *cast_Integer_to_Int8(Value *input);
Value *cast_Integer_to_Int16(Value *input);
Value *cast_Integer_to_Int32(Value *input);
Value *cast_Integer_to_Int64(Value *input);
Value *cast_Integer_to_double(Value *input);
Value *cast_Integer_to_char(Value *input);
Value *cast_Integer_to_string(Value *input);
