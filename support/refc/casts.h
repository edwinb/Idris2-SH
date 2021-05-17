#ifndef __CASTS_H__
#define __CASTS_H__

#include "cBackend.h"
#include <stdio.h>
#include <gmp.h>

Value *cast_Int_to_Bits8(Value *);
Value *cast_Int_to_Bits16(Value *);
Value *cast_Int_to_Bits32(Value *);
Value *cast_Int_to_Bits64(Value *);
Value *cast_Int_to_Integer(Value *);
Value *cast_Int_to_double(Value *);
Value *cast_Int_to_char(Value *);
Value *cast_Int_to_string(Value *);

Value *cast_double_to_Bits8(Value *);
Value *cast_double_to_Bits16(Value *);
Value *cast_double_to_Bits32(Value *);
Value *cast_double_to_Bits64(Value *);
Value *cast_double_to_Int(Value *);
Value *cast_double_to_Integer(Value *);
Value *cast_double_to_char(Value *);
Value *cast_double_to_string(Value *);

Value *cast_char_to_Bits8(Value *);
Value *cast_char_to_Bits16(Value *);
Value *cast_char_to_Bits32(Value *);
Value *cast_char_to_Bits64(Value *);
Value *cast_char_to_Int(Value *);
Value *cast_char_to_Integer(Value *);
Value *cast_char_to_double(Value *);
Value *cast_char_to_string(Value *);

Value *cast_string_to_Bits8(Value *);
Value *cast_string_to_Bits16(Value *);
Value *cast_string_to_Bits32(Value *);
Value *cast_string_to_Bits64(Value *);
Value *cast_string_to_Int(Value *);
Value *cast_string_to_Integer(Value *);
Value *cast_string_to_double(Value *);
Value *cast_string_to_char(Value *);

Value *cast_Bits8_to_Bits16(Value *input);
Value *cast_Bits8_to_Bits32(Value *input);
Value *cast_Bits8_to_Bits64(Value *input);
Value *cast_Bits8_to_Int(Value *input);
Value *cast_Bits8_to_Integer(Value *input);
Value *cast_Bits8_to_double(Value *input);
Value *cast_Bits8_to_char(Value *input);
Value *cast_Bits8_to_string(Value *input);

Value *cast_Bits16_to_Bits8(Value *input);
Value *cast_Bits16_to_Bits32(Value *input);
Value *cast_Bits16_to_Bits64(Value *input);
Value *cast_Bits16_to_Int(Value *input);
Value *cast_Bits16_to_Integer(Value *input);
Value *cast_Bits16_to_double(Value *input);
Value *cast_Bits16_to_char(Value *input);
Value *cast_Bits16_to_string(Value *input);

Value *cast_Bits32_to_Bits8(Value *input);
Value *cast_Bits32_to_Bits16(Value *input);
Value *cast_Bits32_to_Bits64(Value *input);
Value *cast_Bits32_to_Int(Value *input);
Value *cast_Bits32_to_Integer(Value *input);
Value *cast_Bits32_to_double(Value *input);
Value *cast_Bits32_to_char(Value *input);
Value *cast_Bits32_to_string(Value *input);

Value *cast_Bits64_to_Bits8(Value *input);
Value *cast_Bits64_to_Bits16(Value *input);
Value *cast_Bits64_to_Bits32(Value *input);
Value *cast_Bits64_to_Int(Value *input);
Value *cast_Bits64_to_Integer(Value *input);
Value *cast_Bits64_to_double(Value *input);
Value *cast_Bits64_to_char(Value *input);
Value *cast_Bits64_to_string(Value *input);

Value *cast_Integer_to_Bits8(Value *input);
Value *cast_Integer_to_Bits16(Value *input);
Value *cast_Integer_to_Bits32(Value *input);
Value *cast_Integer_to_Bits64(Value *input);
Value *cast_Integer_to_Int(Value *input);
Value *cast_Integer_to_double(Value *input);
Value *cast_Integer_to_char(Value *input);
Value *cast_Integer_to_string(Value *input);

#endif
