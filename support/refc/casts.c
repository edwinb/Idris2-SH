#include "casts.h"
#include <inttypes.h>

/*  conversions from Int8  */
Value *cast_Int8_to_Bits8(Value *input)
{
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeBits8((uint8_t)from->i8);
}

Value *cast_Int8_to_Bits16(Value *input)
{
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeBits16((uint16_t)from->i8);
}

Value *cast_Int8_to_Bits32(Value *input)
{
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeBits32((uint32_t)from->i8);
}

Value *cast_Int8_to_Bits64(Value *input)
{
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeBits64((uint64_t)from->i8);
}

Value *cast_Int8_to_Int16(Value *input)
{
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeInt16((int16_t)from->i8);
}

Value *cast_Int8_to_Int32(Value *input)
{
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeInt32((int32_t)from->i8);
}

Value *cast_Int8_to_Int64(Value *input)
{
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeInt64((int64_t)from->i8);
}

Value *cast_Int8_to_Integer(Value *input)
{
    Value_Int8 *from = (Value_Int8 *)input;

    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_set_si(&retVal->i, from->i8);
#else
    mpz_set_si(retVal->i, from->i8);
#endif

    return (Value *)retVal;
}

Value *cast_Int8_to_double(Value *input)
{
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeDouble((double)from->i8);
}

Value *cast_Int8_to_char(Value *input)
{
    Value_Int8 *from = (Value_Int8 *)input;
    return (Value *)makeChar((unsigned char)from->i8);
}

Value *cast_Int8_to_string(Value *input)
{
    Value_Int8 *from = (Value_Int8 *)input;

    int l = snprintf(NULL, 0, "%" PRId8 "", from->i8);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRId8 "", from->i8);

    return (Value *)retVal;
}

/*  conversions from Int16  */
Value *cast_Int16_to_Bits8(Value *input)
{
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeBits8((uint8_t)from->i16);
}

Value *cast_Int16_to_Bits16(Value *input)
{
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeBits16((uint16_t)from->i16);
}

Value *cast_Int16_to_Bits32(Value *input)
{
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeBits32((uint32_t)from->i16);
}

Value *cast_Int16_to_Bits64(Value *input)
{
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeBits64((uint64_t)from->i16);
}

Value *cast_Int16_to_Int8(Value *input)
{
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeInt8((int8_t)from->i16);
}

Value *cast_Int16_to_Int32(Value *input)
{
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeInt32((int32_t)from->i16);
}

Value *cast_Int16_to_Int64(Value *input)
{
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeInt64((int64_t)from->i16);
}

Value *cast_Int16_to_Integer(Value *input)
{
    Value_Int16 *from = (Value_Int16 *)input;

    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_set_si(&retVal->i, from->i16);
#else
    mpz_set_si(retVal->i, from->i16);
#endif

    return (Value *)retVal;
}

Value *cast_Int16_to_double(Value *input)
{
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeDouble((double)from->i16);
}

Value *cast_Int16_to_char(Value *input)
{
    Value_Int16 *from = (Value_Int16 *)input;
    return (Value *)makeChar((unsigned char)from->i16);
}

Value *cast_Int16_to_string(Value *input)
{
    Value_Int16 *from = (Value_Int16 *)input;

    int l = snprintf(NULL, 0, "%" PRId16 "", from->i16);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRId16 "", from->i16);

    return (Value *)retVal;
}

/*  conversions from Int32  */
Value *cast_Int32_to_Bits8(Value *input)
{
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeBits8((uint8_t)from->i32);
}

Value *cast_Int32_to_Bits16(Value *input)
{
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeBits16((uint16_t)from->i32);
}

Value *cast_Int32_to_Bits32(Value *input)
{
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeBits32((uint32_t)from->i32);
}

Value *cast_Int32_to_Bits64(Value *input)
{
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeBits64((uint64_t)from->i32);
}

Value *cast_Int32_to_Int8(Value *input)
{
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeInt8((int8_t)from->i32);
}

Value *cast_Int32_to_Int16(Value *input)
{
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeInt16((int16_t)from->i32);
}

Value *cast_Int32_to_Int64(Value *input)
{
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeInt64((int64_t)from->i32);
}

Value *cast_Int32_to_Integer(Value *input)
{
    Value_Int32 *from = (Value_Int32 *)input;

    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_set_si(&retVal->i, from->i32);
#else
    mpz_set_si(retVal->i, from->i32);
#endif

    return (Value *)retVal;
}

Value *cast_Int32_to_double(Value *input)
{
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeDouble((double)from->i32);
}

Value *cast_Int32_to_char(Value *input)
{
    Value_Int32 *from = (Value_Int32 *)input;
    return (Value *)makeChar((unsigned char)from->i32);
}

Value *cast_Int32_to_string(Value *input)
{
    Value_Int32 *from = (Value_Int32 *)input;

    int l = snprintf(NULL, 0, "%" PRId32 "", from->i32);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRId32 "", from->i32);

    return (Value *)retVal;
}

/*  conversions from Int64  */
Value *cast_Int64_to_Bits8(Value *input)
{
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeBits8((uint8_t)from->i64);
}

Value *cast_Int64_to_Bits16(Value *input)
{
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeBits16((uint16_t)from->i64);
}

Value *cast_Int64_to_Bits32(Value *input)
{
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeBits32((uint32_t)from->i64);
}

Value *cast_Int64_to_Bits64(Value *input)
{
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeBits64((uint64_t)from->i64);
}

Value *cast_Int64_to_Int8(Value *input)
{
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeInt8((int8_t)from->i64);
}

Value *cast_Int64_to_Int16(Value *input)
{
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeInt16((int16_t)from->i64);
}

Value *cast_Int64_to_Int32(Value *input)
{
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeInt32((int32_t)from->i64);
}

Value *cast_Int64_to_Int64(Value *input)
{
    // Identity cast required as Value_Int64 represents both Int and Int64 types
    return newReference(input);
}

Value *cast_Int64_to_Integer(Value *input)
{
    Value_Int64 *from = (Value_Int64 *)input;

    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_set_si(&retVal->i, from->i64);
#else
    mpz_set_si(retVal->i, from->i64);
#endif

    return (Value *)retVal;
}

Value *cast_Int64_to_double(Value *input)
{
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeDouble((double)from->i64);
}

Value *cast_Int64_to_char(Value *input)
{
    Value_Int64 *from = (Value_Int64 *)input;
    return (Value *)makeChar((unsigned char)from->i64);
}

Value *cast_Int64_to_string(Value *input)
{
    Value_Int64 *from = (Value_Int64 *)input;

    int l = snprintf(NULL, 0, "%" PRId64 "", from->i64);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRId64 "", from->i64);

    return (Value *)retVal;
}

Value *cast_double_to_Bits8(Value *input)
{
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeBits8((uint8_t)from->d);
}

Value *cast_double_to_Bits16(Value *input)
{
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeBits16((uint16_t)from->d);
}

Value *cast_double_to_Bits32(Value *input)
{
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeBits32((uint32_t)from->d);
}

Value *cast_double_to_Bits64(Value *input)
{
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeBits64((uint64_t)from->d);
}

Value *cast_double_to_Int8(Value *input)
{
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeInt8((int8_t)from->d);
}

Value *cast_double_to_Int16(Value *input)
{
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeInt16((int16_t)from->d);
}

Value *cast_double_to_Int32(Value *input)
{
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeInt32((int32_t)from->d);
}

Value *cast_double_to_Int64(Value *input)
{
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeInt64((int64_t)from->d);
}

Value *cast_double_to_Integer(Value *input)
{
    Value_Double *from = (Value_Double *)input;

    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_set_float64(&retVal->i, from->d);
#else
    mpz_set_d(retVal->i, from->d);
#endif

    return (Value *)retVal;
}

Value *cast_double_to_char(Value *input)
{
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeChar((unsigned char)from->d);
}

Value *cast_double_to_string(Value *input)
{
    Value_Double *from = (Value_Double *)input;

    int l = snprintf(NULL, 0, "%f", from->d);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%f", from->d);

    return (Value *)retVal;
}

Value *cast_char_to_Bits8(Value *input)
{
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeBits8((uint8_t)from->c);
}

Value *cast_char_to_Bits16(Value *input)
{
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeBits16((uint16_t)from->c);
}

Value *cast_char_to_Bits32(Value *input)
{
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeBits32((uint32_t)from->c);
}

Value *cast_char_to_Bits64(Value *input)
{
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeBits64((uint64_t)from->c);
}

Value *cast_char_to_Int8(Value *input)
{
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeInt8((int8_t)from->c);
}

Value *cast_char_to_Int16(Value *input)
{
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeInt16((int16_t)from->c);
}

Value *cast_char_to_Int32(Value *input)
{
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeInt32((int32_t)from->c);
}

Value *cast_char_to_Int64(Value *input)
{
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeInt64((int64_t)from->c);
}

Value *cast_char_to_Integer(Value *input)
{
	Value_Char *from = (Value_Char *)input;

	Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_set_si(&retVal->i, from->c);
#else
    mpz_set_si(retVal->i, from->c);
#endif

	return (Value *)retVal;
}

Value *cast_char_to_double(Value *input)
{
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeDouble((unsigned char)from->c);
}

Value *cast_char_to_string(Value *input)
{
    Value_Char *from = (Value_Char *)input;

    Value_String *retVal = makeEmptyString(2);
    retVal->str[0] = from->c;

    return (Value *)retVal;
}

Value *cast_string_to_Bits8(Value *input)
{
    Value_String *from = (Value_String *)input;
    return (Value *)makeBits8((uint8_t)atoi(from->str));
}

Value *cast_string_to_Bits16(Value *input)
{
    Value_String *from = (Value_String *)input;
    return (Value *)makeBits16((uint16_t)atoi(from->str));
}

Value *cast_string_to_Bits32(Value *input)
{
    Value_String *from = (Value_String *)input;
    return (Value *)makeBits32((uint32_t)atoi(from->str));
}

Value *cast_string_to_Bits64(Value *input)
{
    Value_String *from = (Value_String *)input;
    return (Value *)makeBits64((uint64_t)atoi(from->str));
}

Value *cast_string_to_Int8(Value *input)
{
    Value_String *from = (Value_String *)input;
    return (Value *)makeInt8((int8_t)atoi(from->str));
}

Value *cast_string_to_Int16(Value *input)
{
    Value_String *from = (Value_String *)input;
    return (Value *)makeInt16((int16_t)atoi(from->str));
}

Value *cast_string_to_Int32(Value *input)
{
    Value_String *from = (Value_String *)input;
    return (Value *)makeInt32((int32_t)atoi(from->str));
}

Value *cast_string_to_Int64(Value *input)
{
    Value_String *from = (Value_String *)input;
    return (Value *)makeInt64((int64_t)atoi(from->str));
}

Value *cast_string_to_Integer(Value *input)
{
    Value_String *from = (Value_String *)input;

    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_atof(&retVal->i, from->str, NULL, 10, BF_PREC_INF, BF_RNDZ);
#else
    mpz_set_str(retVal->i, from->str, 10);
#endif

    return (Value *)retVal;
}

Value *cast_string_to_double(Value *input)
{
    Value_Double *retVal = IDRIS2_NEW_VALUE(Value_Double);
    retVal->header.tag = DOUBLE_TAG;
    Value_String *from = (Value_String *)input;
    retVal->d = atof(from->str);

    return (Value *)retVal;
}

Value *cast_string_to_char(Value *input)
{
    Value_Char *retVal = IDRIS2_NEW_VALUE(Value_Char);
    retVal->header.tag = CHAR_TAG;
    Value_String *from = (Value_String *)input;
    retVal->c = from->str[0];

    return (Value *)retVal;
}

/*  conversions from Bits8  */
Value *cast_Bits8_to_Bits16(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeBits16((uint16_t)from->ui8);
}

Value *cast_Bits8_to_Bits32(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeBits32((uint32_t)from->ui8);
}

Value *cast_Bits8_to_Bits64(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeBits64((uint64_t)from->ui8);
}

Value *cast_Bits8_to_Int8(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeInt8((int8_t)from->ui8);
}

Value *cast_Bits8_to_Int16(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeInt16((int16_t)from->ui8);
}

Value *cast_Bits8_to_Int32(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeInt32((int32_t)from->ui8);
}

Value *cast_Bits8_to_Int64(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeInt64((int64_t)from->ui8);
}

Value *cast_Bits8_to_Integer(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;

    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_set_ui(&retVal->i, from->ui8);
#else
    mpz_set_ui(retVal->i, from->ui8);
#endif

    return (Value *)retVal;
}

Value *cast_Bits8_to_double(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeDouble((double)from->ui8);
}

Value *cast_Bits8_to_char(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeChar((unsigned char)from->ui8);
}

Value *cast_Bits8_to_string(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;

    int l = snprintf(NULL, 0, "%" PRIu8 "", from->ui8);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRIu8 "", from->ui8);

    return (Value *)retVal;
}

/*  conversions from Bits16  */
Value *cast_Bits16_to_Bits8(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeBits8((uint8_t)from->ui16);
}

Value *cast_Bits16_to_Bits32(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeBits32((uint32_t)from->ui16);
}

Value *cast_Bits16_to_Bits64(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeBits64((uint64_t)from->ui16);
}

Value *cast_Bits16_to_Int8(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeInt8((int8_t)from->ui16);
}

Value *cast_Bits16_to_Int16(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeInt16((int16_t)from->ui16);
}

Value *cast_Bits16_to_Int32(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeInt32((int32_t)from->ui16);
}

Value *cast_Bits16_to_Int64(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeInt64((int64_t)from->ui16);
}

Value *cast_Bits16_to_Integer(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;

    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_set_ui(&retVal->i, from->ui16);
#else
    mpz_set_ui(retVal->i, from->ui16);
#endif

    return (Value *)retVal;
}

Value *cast_Bits16_to_double(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeDouble((double)from->ui16);
}

Value *cast_Bits16_to_char(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeChar((unsigned char)from->ui16);
}

Value *cast_Bits16_to_string(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;

    int l = snprintf(NULL, 0, "%" PRIu16 "", from->ui16);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRIu16 "", from->ui16);

    return (Value *)retVal;
}

/*  conversions from Bits32  */
Value *cast_Bits32_to_Bits8(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeBits8((uint8_t)from->ui32);
}

Value *cast_Bits32_to_Bits16(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeBits16((uint16_t)from->ui32);
}

Value *cast_Bits32_to_Bits64(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeBits64((uint64_t)from->ui32);
}

Value *cast_Bits32_to_Int8(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeInt8((int8_t)from->ui32);
}

Value *cast_Bits32_to_Int16(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeInt16((int16_t)from->ui32);
}

Value *cast_Bits32_to_Int32(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeInt32((int32_t)from->ui32);
}

Value *cast_Bits32_to_Int64(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeInt64((int64_t)from->ui32);
}

Value *cast_Bits32_to_Integer(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;

    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_set_ui(&retVal->i, from->ui32);
#else
    mpz_set_ui(retVal->i, from->ui32);
#endif

    return (Value *)retVal;
}

Value *cast_Bits32_to_double(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeDouble((double)from->ui32);
}

Value *cast_Bits32_to_char(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeChar((unsigned char)from->ui32);
}

Value *cast_Bits32_to_string(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;

    int l = snprintf(NULL, 0, "%" PRIu32 "", from->ui32);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRIu32 "", from->ui32);

    return (Value *)retVal;
}

/*  conversions from Bits64  */
Value *cast_Bits64_to_Bits8(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeBits8((uint8_t)from->ui64);
}

Value *cast_Bits64_to_Bits16(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeBits16((uint16_t)from->ui64);
}

Value *cast_Bits64_to_Bits32(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeBits32((uint32_t)from->ui64);
}

Value *cast_Bits64_to_Int8(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeInt8((int8_t)from->ui64);
}

Value *cast_Bits64_to_Int16(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeInt16((int16_t)from->ui64);
}

Value *cast_Bits64_to_Int32(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeInt32((int32_t)from->ui64);
}

Value *cast_Bits64_to_Int64(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeInt64((int64_t)from->ui64);
}

Value *cast_Bits64_to_Integer(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;

    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_set_ui(&retVal->i, from->ui64);
#else
    mpz_set_ui(retVal->i, from->ui64);
#endif

    return (Value *)retVal;
}

Value *cast_Bits64_to_double(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeDouble((double)from->ui64);
}

Value *cast_Bits64_to_char(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeChar((unsigned char)from->ui64);
}

Value *cast_Bits64_to_string(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;

    int l = snprintf(NULL, 0, "%" PRIu64 "", from->ui64);
    Value_String *retVal = makeEmptyString(l + 1);
    sprintf(retVal->str, "%" PRIu64 "", from->ui64);

    return (Value *)retVal;
}

/*  conversions from Integer */
#ifdef INTEGER_USE_LIBBF
uint64_t get_lsb(bf_t i, int b)
{
    bf_t e, q, r;
    uint64_t res;
    bf_init(i.ctx, &e);
    bf_init(i.ctx, &q);
    bf_init(i.ctx, &r);
    bf_set_ui(&e, 1);
    bf_mul_2exp(&e, b, BF_PREC_INF, BF_RNDZ);
    bf_rem(&r, &i, &e, BF_PREC_INF, 0, BF_DIVREM_EUCLIDIAN);
    bf_get_uint64(&res, &r);
    return res;
}
#else
uint64_t get_lsb(mpz_t i, mp_bitcnt_t b)
{
    mpz_t r;
    mpz_init(r);
    mpz_fdiv_r_2exp(r, i, b);
    uint64_t retVal = mpz_get_ui(r);
    mpz_clear(r);
    return retVal;
}
#endif

Value *cast_Integer_to_Bits8(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeBits8((uint8_t)get_lsb(from->i, 8));
}

Value *cast_Integer_to_Bits16(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeBits16((uint16_t)get_lsb(from->i, 16));
}

Value *cast_Integer_to_Bits32(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeBits32((uint32_t)get_lsb(from->i, 32));
}

Value *cast_Integer_to_Bits64(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeBits64((uint64_t)get_lsb(from->i, 64));
}

Value *cast_Integer_to_Int8(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeInt8((int8_t)get_lsb(from->i, 8));
}

Value *cast_Integer_to_Int16(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeInt16((int16_t)get_lsb(from->i, 16));
}

Value *cast_Integer_to_Int32(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeInt32((int32_t)get_lsb(from->i, 32));
}

Value *cast_Integer_to_Int64(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeInt64((int64_t)get_lsb(from->i, 64));
}

Value *cast_Integer_to_double(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
#ifdef INTEGER_USE_LIBBF
    double res;
    bf_get_float64(&from->i, &res, BF_RNDN);
    return (Value*)makeDouble(res);
#else
    return (Value *)makeDouble(mpz_get_d(from->i));
#endif
}

Value *cast_Integer_to_char(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeChar((unsigned char)get_lsb(from->i, 8));
}

Value *cast_Integer_to_string(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;

    Value_String *retVal = IDRIS2_NEW_VALUE(Value_String);
    retVal->header.tag = STRING_TAG;
#ifdef INTEGER_USE_LIBBF
    retVal->str = bf_ftoa(NULL, &from->i, 10, 0, BF_RNDZ | BF_FTOA_FORMAT_FRAC);
#else
    retVal->str = mpz_get_str(NULL, 10, from->i);
#endif

    return (Value *)retVal;
}
