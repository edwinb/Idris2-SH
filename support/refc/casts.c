#include "casts.h"
#include <inttypes.h>

/*  conversions from Int8  */
Value *cast_Int8_to_Bits8(Value *input) {
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeBits8((uint8_t)from->i8);
}

Value *cast_Int8_to_Bits16(Value *input) {
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeBits16((uint16_t)from->i8);
}

Value *cast_Int8_to_Bits32(Value *input) {
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeBits32((uint32_t)from->i8);
}

Value *cast_Int8_to_Bits64(Value *input) {
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeBits64((uint64_t)from->i8);
}

Value *cast_Int8_to_Int16(Value *input) {
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeInt16((int16_t)from->i8);
}

Value *cast_Int8_to_Int32(Value *input) {
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeInt32((int32_t)from->i8);
}

Value *cast_Int8_to_Int64(Value *input) {
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeInt64((int64_t)from->i8);
}

Value *cast_Int8_to_Integer(Value *input) {
    Value_Int8 *from = (Value_Int8 *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_si(retVal->i, from->i8);

    return (Value *)retVal;
}

Value *cast_Int8_to_double(Value *input) {
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeDouble((double)from->i8);
}

Value *cast_Int8_to_char(Value *input) {
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeChar((unsigned char)from->i8);
}

Value *cast_Int8_to_string(Value *input) {
    Value_Int8 *from = (Value_Int8 *)input;

    int l = snprintf(NULL, 0, "%" PRId8 "", from->i8);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRId8 "", from->i8);

    return (Value *)retVal;
}

/*  conversions from Int16  */
Value *cast_Int16_to_Bits8(Value *input) {
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeBits8((uint8_t)from->i16);
}

Value *cast_Int16_to_Bits16(Value *input) {
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeBits16((uint16_t)from->i16);
}

Value *cast_Int16_to_Bits32(Value *input) {
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeBits32((uint32_t)from->i16);
}

Value *cast_Int16_to_Bits64(Value *input) {
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeBits64((uint64_t)from->i16);
}

Value *cast_Int16_to_Int8(Value *input) {
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeInt8((int8_t)from->i16);
}

Value *cast_Int16_to_Int32(Value *input) {
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeInt32((int32_t)from->i16);
}

Value *cast_Int16_to_Int64(Value *input) {
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeInt64((int64_t)from->i16);
}

Value *cast_Int16_to_Integer(Value *input) {
    Value_Int16 *from = (Value_Int16 *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_si(retVal->i, from->i16);

    return (Value *)retVal;
}

Value *cast_Int16_to_double(Value *input) {
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeDouble((double)from->i16);
}

Value *cast_Int16_to_char(Value *input) {
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeChar((unsigned char)from->i16);
}

Value *cast_Int16_to_string(Value *input) {
    Value_Int16 *from = (Value_Int16 *)input;

    int l = snprintf(NULL, 0, "%" PRId16 "", from->i16);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRId16 "", from->i16);

    return (Value *)retVal;
}

/*  conversions from Int32  */
Value *cast_Int32_to_Bits8(Value *input) {
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeBits8((uint8_t)from->i32);
}

Value *cast_Int32_to_Bits16(Value *input) {
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeBits16((uint16_t)from->i32);
}

Value *cast_Int32_to_Bits32(Value *input) {
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeBits32((uint32_t)from->i32);
}

Value *cast_Int32_to_Bits64(Value *input) {
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeBits64((uint64_t)from->i32);
}

Value *cast_Int32_to_Int8(Value *input) {
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeInt8((int8_t)from->i32);
}

Value *cast_Int32_to_Int16(Value *input) {
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeInt16((int16_t)from->i32);
}

Value *cast_Int32_to_Int64(Value *input) {
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeInt64((int64_t)from->i32);
}

Value *cast_Int32_to_Integer(Value *input) {
    Value_Int32 *from = (Value_Int32 *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_si(retVal->i, from->i32);

    return (Value *)retVal;
}

Value *cast_Int32_to_double(Value *input) {
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeDouble((double)from->i32);
}

Value *cast_Int32_to_char(Value *input) {
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeChar((unsigned char)from->i32);
}

Value *cast_Int32_to_string(Value *input) {
    Value_Int32 *from = (Value_Int32 *)input;

    int l = snprintf(NULL, 0, "%" PRId32 "", from->i32);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRId32 "", from->i32);

    return (Value *)retVal;
}

/*  conversions from Int64  */
Value *cast_Int64_to_Bits8(Value *input) {
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeBits8((uint8_t)from->i64);
}

Value *cast_Int64_to_Bits16(Value *input) {
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeBits16((uint16_t)from->i64);
}

Value *cast_Int64_to_Bits32(Value *input) {
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeBits32((uint32_t)from->i64);
}

Value *cast_Int64_to_Bits64(Value *input) {
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeBits64((uint64_t)from->i64);
}

Value *cast_Int64_to_Int8(Value *input) {
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeInt8((int8_t)from->i64);
}

Value *cast_Int64_to_Int16(Value *input) {
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeInt16((int16_t)from->i64);
}

Value *cast_Int64_to_Int32(Value *input) {
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeInt32((int32_t)from->i64);
}

Value *cast_Int64_to_Int64(Value *input) {
    // Identity cast required as Value_Int64 represents both Int and Int64 types
    return newReference(input);
}

Value *cast_Int64_to_Integer(Value *input) {
    Value_Int64 *from = (Value_Int64 *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_si(retVal->i, from->i64);

    return (Value *)retVal;
}

Value *cast_Int64_to_double(Value *input) {
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeDouble((double)from->i64);
}

Value *cast_Int64_to_char(Value *input) {
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeChar((unsigned char)from->i64);
}

Value *cast_Int64_to_string(Value *input) {
    Value_Int64 *from = (Value_Int64 *)input;

    int l = snprintf(NULL, 0, "%" PRId64 "", from->i64);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRId64 "", from->i64);

    return (Value *)retVal;
}

Value *cast_double_to_Bits8(Value *input) {
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeBits8((uint8_t)from->d);
}

Value *cast_double_to_Bits16(Value *input) {
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeBits16((uint16_t)from->d);
}

Value *cast_double_to_Bits32(Value *input) {
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeBits32((uint32_t)from->d);
}

Value *cast_double_to_Bits64(Value *input) {
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeBits64((uint64_t)from->d);
}

Value *cast_double_to_Int8(Value *input) {
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeInt8((int8_t)from->d);
}

Value *cast_double_to_Int16(Value *input) {
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeInt16((int16_t)from->d);
}

Value *cast_double_to_Int32(Value *input) {
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeInt32((int32_t)from->d);
}

Value *cast_double_to_Int64(Value *input) {
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeInt64((int64_t)from->d);
}

Value *cast_double_to_Integer(Value *input) {
    Value_Double *from = (Value_Double *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_d(retVal->i, from->d);

    return (Value *)retVal;
}

Value *cast_double_to_char(Value *input) {
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeChar((unsigned char)from->d);
}

Value *cast_double_to_string(Value *input) {
    Value_Double *from = (Value_Double *)input;

    int l = snprintf(NULL, 0, "%f", from->d);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%f", from->d);

    return (Value *)retVal;
}

Value *cast_char_to_Bits8(Value *input) {
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeBits8((uint8_t)from->c);
}

Value *cast_char_to_Bits16(Value *input) {
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeBits16((uint16_t)from->c);
}

Value *cast_char_to_Bits32(Value *input) {
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeBits32((uint32_t)from->c);
}

Value *cast_char_to_Bits64(Value *input) {
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeBits64((uint64_t)from->c);
}

Value *cast_char_to_Int8(Value *input) {
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeInt8((int8_t)from->c);
}

Value *cast_char_to_Int16(Value *input) {
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeInt16((int16_t)from->c);
}

Value *cast_char_to_Int32(Value *input) {
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeInt32((int32_t)from->c);
}

Value *cast_char_to_Int64(Value *input) {
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeInt64((int64_t)from->c);
}

Value *cast_char_to_Integer(Value *input) {
    Value_Char *from = (Value_Char *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_si(retVal->i, from->c);

    return (Value *)retVal;
}

Value *cast_char_to_double(Value *input) {
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeDouble((unsigned char)from->c);
}

Value *cast_char_to_string(Value *input) {
    Value_Char *from = (Value_Char *)input;

    Value_String *retVal = makeEmptyString(2);
    retVal->str[0] = from->c;

    return (Value *)retVal;
}

Value *cast_string_to_Bits8(Value *input) {
    Value_String *from = (Value_String *)input;
    return (Value *)makeBits8((uint8_t)atoi(from->str));
}

Value *cast_string_to_Bits16(Value *input) {
    Value_String *from = (Value_String *)input;
    return (Value *)makeBits16((uint16_t)atoi(from->str));
}

Value *cast_string_to_Bits32(Value *input) {
    Value_String *from = (Value_String *)input;
    return (Value *)makeBits32((uint32_t)atoi(from->str));
}

Value *cast_string_to_Bits64(Value *input) {
    Value_String *from = (Value_String *)input;
    return (Value *)makeBits64((uint64_t)atoi(from->str));
}

Value *cast_string_to_Int8(Value *input) {
    Value_String *from = (Value_String *)input;
    return (Value *)makeInt8((int8_t)atoi(from->str));
}

Value *cast_string_to_Int16(Value *input) {
    Value_String *from = (Value_String *)input;
    return (Value *)makeInt16((int16_t)atoi(from->str));
}

Value *cast_string_to_Int32(Value *input) {
    Value_String *from = (Value_String *)input;
    return (Value *)makeInt32((int32_t)atoi(from->str));
}

Value *cast_string_to_Int64(Value *input) {
    Value_String *from = (Value_String *)input;
    return (Value *)makeInt64((int64_t)atoi(from->str));
}

Value *cast_string_to_Integer(Value *input) {
    Value_String *from = (Value_String *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_str(retVal->i, from->str, 10);

    return (Value *)retVal;
}

Value *cast_string_to_double(Value *input) {
    Value_Double *retVal = (Value_Double *)newValue();
    retVal->header.tag = DOUBLE_TAG;
    Value_String *from = (Value_String *)input;
    retVal->d = atof(from->str);

    return (Value *)retVal;
}

Value *cast_string_to_char(Value *input) {
    Value_Char *retVal = (Value_Char *)newValue();
    retVal->header.tag = CHAR_TAG;
    Value_String *from = (Value_String *)input;
    retVal->c = from->str[0];

    return (Value *)retVal;
}

/*  conversions from Bits8  */
Value *cast_Bits8_to_Bits16(Value *input) {
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeBits16((uint16_t)from->ui8);
}

Value *cast_Bits8_to_Bits32(Value *input) {
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeBits32((uint32_t)from->ui8);
}

Value *cast_Bits8_to_Bits64(Value *input) {
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeBits64((uint64_t)from->ui8);
}

Value *cast_Bits8_to_Int8(Value *input) {
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeInt8((int8_t)from->ui8);
}

Value *cast_Bits8_to_Int16(Value *input) {
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeInt16((int16_t)from->ui8);
}

Value *cast_Bits8_to_Int32(Value *input) {
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeInt32((int32_t)from->ui8);
}

Value *cast_Bits8_to_Int64(Value *input) {
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeInt64((int64_t)from->ui8);
}

Value *cast_Bits8_to_Integer(Value *input) {
    Value_Bits8 *from = (Value_Bits8 *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_ui(retVal->i, from->ui8);

    return (Value *)retVal;
}

Value *cast_Bits8_to_double(Value *input) {
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeDouble((double)from->ui8);
}

Value *cast_Bits8_to_char(Value *input) {
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeChar((unsigned char)from->ui8);
}

Value *cast_Bits8_to_string(Value *input) {
    Value_Bits8 *from = (Value_Bits8 *)input;

    int l = snprintf(NULL, 0, "%" PRIu8 "", from->ui8);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRIu8 "", from->ui8);

    return (Value *)retVal;
}

/*  conversions from Bits16  */
Value *cast_Bits16_to_Bits8(Value *input) {
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeBits8((uint8_t)from->ui16);
}

Value *cast_Bits16_to_Bits32(Value *input) {
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeBits32((uint32_t)from->ui16);
}

Value *cast_Bits16_to_Bits64(Value *input) {
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeBits64((uint64_t)from->ui16);
}

Value *cast_Bits16_to_Int8(Value *input) {
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeInt8((int8_t)from->ui16);
}

Value *cast_Bits16_to_Int16(Value *input) {
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeInt16((int16_t)from->ui16);
}

Value *cast_Bits16_to_Int32(Value *input) {
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeInt32((int32_t)from->ui16);
}

Value *cast_Bits16_to_Int64(Value *input) {
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeInt64((int64_t)from->ui16);
}

Value *cast_Bits16_to_Integer(Value *input) {
    Value_Bits16 *from = (Value_Bits16 *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_ui(retVal->i, from->ui16);

    return (Value *)retVal;
}

Value *cast_Bits16_to_double(Value *input) {
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeDouble((double)from->ui16);
}

Value *cast_Bits16_to_char(Value *input) {
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeChar((unsigned char)from->ui16);
}

Value *cast_Bits16_to_string(Value *input) {
    Value_Bits16 *from = (Value_Bits16 *)input;

    int l = snprintf(NULL, 0, "%" PRIu16 "", from->ui16);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRIu16 "", from->ui16);

    return (Value *)retVal;
}

/*  conversions from Bits32  */
Value *cast_Bits32_to_Bits8(Value *input) {
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeBits8((uint8_t)from->ui32);
}

Value *cast_Bits32_to_Bits16(Value *input) {
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeBits16((uint16_t)from->ui32);
}

Value *cast_Bits32_to_Bits64(Value *input) {
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeBits64((uint64_t)from->ui32);
}

Value *cast_Bits32_to_Int8(Value *input) {
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeInt8((int8_t)from->ui32);
}

Value *cast_Bits32_to_Int16(Value *input) {
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeInt16((int16_t)from->ui32);
}

Value *cast_Bits32_to_Int32(Value *input) {
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeInt32((int32_t)from->ui32);
}

Value *cast_Bits32_to_Int64(Value *input) {
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeInt64((int64_t)from->ui32);
}

Value *cast_Bits32_to_Integer(Value *input) {
    Value_Bits32 *from = (Value_Bits32 *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_ui(retVal->i, from->ui32);

    return (Value *)retVal;
}

Value *cast_Bits32_to_double(Value *input) {
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeDouble((double)from->ui32);
}

Value *cast_Bits32_to_char(Value *input) {
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeChar((unsigned char)from->ui32);
}

Value *cast_Bits32_to_string(Value *input) {
    Value_Bits32 *from = (Value_Bits32 *)input;

    int l = snprintf(NULL, 0, "%" PRIu32 "", from->ui32);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRIu32 "", from->ui32);

    return (Value *)retVal;
}

/*  conversions from Bits64  */
Value *cast_Bits64_to_Bits8(Value *input) {
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeBits8((uint8_t)from->ui64);
}

Value *cast_Bits64_to_Bits16(Value *input) {
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeBits16((uint16_t)from->ui64);
}

Value *cast_Bits64_to_Bits32(Value *input) {
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeBits32((uint32_t)from->ui64);
}

Value *cast_Bits64_to_Int8(Value *input) {
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeInt8((int8_t)from->ui64);
}

Value *cast_Bits64_to_Int16(Value *input) {
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeInt16((int16_t)from->ui64);
}

Value *cast_Bits64_to_Int32(Value *input) {
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeInt32((int32_t)from->ui64);
}

Value *cast_Bits64_to_Int64(Value *input) {
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeInt64((int64_t)from->ui64);
}

Value *cast_Bits64_to_Integer(Value *input) {
    Value_Bits64 *from = (Value_Bits64 *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_ui(retVal->i, from->ui64);

    return (Value *)retVal;
}

Value *cast_Bits64_to_double(Value *input) {
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeDouble((double)from->ui64);
}

Value *cast_Bits64_to_char(Value *input) {
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeChar((unsigned char)from->ui64);
}

Value *cast_Bits64_to_string(Value *input) {
    Value_Bits64 *from = (Value_Bits64 *)input;

    int l = snprintf(NULL, 0, "%" PRIu64 "", from->ui64);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRIu64 "", from->ui64);

    return (Value *)retVal;
}

/*  conversions from Integer */
uint64_t mpz_get_lsb(mpz_t i, mp_bitcnt_t b) {
    mpz_t r;
    mpz_init(r);
    mpz_fdiv_r_2exp(r, i, b);
    uint64_t retVal = mpz_get_ui(r);
    mpz_clear(r);
    return retVal;
}

Value *cast_Integer_to_Bits8(Value *input) {
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeBits8((uint8_t)mpz_get_lsb(from->i, 8));
}

Value *cast_Integer_to_Bits16(Value *input) {
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeBits16((uint16_t)mpz_get_lsb(from->i, 16));
}

Value *cast_Integer_to_Bits32(Value *input) {
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeBits32((uint32_t)mpz_get_lsb(from->i, 32));
}

Value *cast_Integer_to_Bits64(Value *input) {
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeBits64((uint64_t)mpz_get_lsb(from->i, 64));
}

Value *cast_Integer_to_Int8(Value *input) {
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeInt8((int8_t)mpz_get_lsb(from->i, 8));
}

Value *cast_Integer_to_Int16(Value *input) {
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeInt16((int16_t)mpz_get_lsb(from->i, 16));
}

Value *cast_Integer_to_Int32(Value *input) {
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeInt32((int32_t)mpz_get_lsb(from->i, 32));
}

Value *cast_Integer_to_Int64(Value *input) {
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeInt64((int64_t)mpz_get_lsb(from->i, 64));
}

Value *cast_Integer_to_double(Value *input) {
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeDouble(mpz_get_d(from->i));
}

Value *cast_Integer_to_char(Value *input) {
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeChar((unsigned char)mpz_get_lsb(from->i, 8));
}

Value *cast_Integer_to_string(Value *input) {
    Value_Integer *from = (Value_Integer *)input;

    Value_String *retVal = (Value_String *)newValue();
    retVal->header.tag = STRING_TAG;
    retVal->str = mpz_get_str(NULL, 10, from->i);

    return (Value *)retVal;
}
