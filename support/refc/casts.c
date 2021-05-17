#include "casts.h"
#include <inttypes.h>

Value *cast_Int_to_Bits8(Value *input)
{
    Value_Int *from = (Value_Int *)input;
    return (Value *)makeBits8((uint8_t)from->i64);
}

Value *cast_Int_to_Bits16(Value *input)
{
    Value_Int *from = (Value_Int *)input;
    return (Value *)makeBits16((uint16_t)from->i64);
}

Value *cast_Int_to_Bits32(Value *input)
{
    Value_Int *from = (Value_Int *)input;
    return (Value *)makeBits32((uint32_t)from->i64);
}

Value *cast_Int_to_Bits64(Value *input)
{
    Value_Int *from = (Value_Int *)input;
    return (Value *)makeBits64((uint64_t)from->i64);
}

Value *cast_Int_to_Integer(Value *input)
{
    Value_Int *from = (Value_Int *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_si(retVal->i, from->i64);

    return (Value *)retVal;
}

Value *cast_Int_to_double(Value *input)
{
    Value_Int *from = (Value_Int *)input;
    return (Value *)makeDouble((int64_t)from->i64);
}

Value *cast_Int_to_char(Value *input)
{
    Value_Int *from = (Value_Int *)input;
    return (Value *)makeChar((int64_t)from->i64);
}

Value *cast_Int_to_string(Value *input)
{
    Value_Int *from = (Value_Int *)input;

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

Value *cast_double_to_Int(Value *input)
{
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeInt((int64_t)from->d);
}

Value *cast_double_to_Integer(Value *input)
{
    Value_Double *from = (Value_Double *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_d(retVal->i, from->d);

    return (Value *)retVal;
}

Value *cast_double_to_char(Value *input)
{
    Value_Double *from = (Value_Double *)input;
    return (Value *)makeChar((double)from->d);
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

Value *cast_char_to_Int(Value *input)
{
    Value_Char *from = (Value_Char *)input;
    return (Value *)makeInt((int64_t)from->c);
}

Value *cast_char_to_Integer(Value *input)
{
	Value_Char *from = (Value_Char *)input;

	Value_Integer *retVal = makeInteger();
	mpz_set_si(retVal->i, from->c);

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

Value *cast_string_to_Int(Value *input)
{
    Value_String *from = (Value_String *)input;
    return (Value *)makeInt((int64_t)atoi(from->str));
}

Value *cast_string_to_Integer(Value *input)
{
    Value_String *from = (Value_String *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_str(retVal->i, from->str, 10);

    return (Value *)retVal;
}

Value *cast_string_to_double(Value *input)
{
    Value_Double *retVal = (Value_Double *)newValue();
    retVal->header.tag = DOUBLE_TAG;
    Value_String *from = (Value_String *)input;
    retVal->d = atof(from->str);

    return (Value *)retVal;
}

Value *cast_string_to_char(Value *input)
{
    Value_Char *retVal = (Value_Char *)newValue();
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

Value *cast_Bits8_to_Int(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeInt((int64_t)from->ui8);
}

Value *cast_Bits8_to_Integer(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_ui(retVal->i, from->ui8);

    return (Value *)retVal;
}

Value *cast_Bits8_to_double(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeDouble((uint8_t)from->ui8);
}

Value *cast_Bits8_to_char(Value *input)
{
    Value_Bits8 *from = (Value_Bits8 *)input;
    return (Value *)makeChar((uint8_t)from->ui8);
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

Value *cast_Bits16_to_Int(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeInt((int64_t)from->ui16);
}

Value *cast_Bits16_to_Integer(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_ui(retVal->i, from->ui16);

    return (Value *)retVal;
}

Value *cast_Bits16_to_double(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeDouble((uint16_t)from->ui16);
}

Value *cast_Bits16_to_char(Value *input)
{
    Value_Bits16 *from = (Value_Bits16 *)input;
    return (Value *)makeChar((uint16_t)from->ui16);
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

Value *cast_Bits32_to_Int(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeInt((int64_t)from->ui32);
}

Value *cast_Bits32_to_Integer(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_ui(retVal->i, from->ui32);

    return (Value *)retVal;
}

Value *cast_Bits32_to_double(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeDouble((uint32_t)from->ui32);
}

Value *cast_Bits32_to_char(Value *input)
{
    Value_Bits32 *from = (Value_Bits32 *)input;
    return (Value *)makeChar((uint32_t)from->ui32);
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

Value *cast_Bits64_to_Int(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeInt((int64_t)from->ui64);
}

Value *cast_Bits64_to_Integer(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;

    Value_Integer *retVal = makeInteger();
    mpz_set_ui(retVal->i, from->ui64);

    return (Value *)retVal;
}

Value *cast_Bits64_to_double(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeDouble((uint64_t)from->ui64);
}

Value *cast_Bits64_to_char(Value *input)
{
    Value_Bits64 *from = (Value_Bits64 *)input;
    return (Value *)makeChar((uint64_t)from->ui64);
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
uint64_t mpz_get_lsb(mpz_t i, mp_bitcnt_t b)
{
    mpz_t r;
    mpz_init(r);
    mpz_fdiv_r_2exp(r, i, b);
    uint64_t retVal = mpz_get_ui(r);
    mpz_clear(r);
    return retVal;
}

Value *cast_Integer_to_Bits8(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeBits8((uint8_t)mpz_get_lsb(from->i, 8));
}

Value *cast_Integer_to_Bits16(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeBits16((uint16_t)mpz_get_lsb(from->i, 16));
}

Value *cast_Integer_to_Bits32(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeBits32((uint32_t)mpz_get_lsb(from->i, 32));
}

Value *cast_Integer_to_Bits64(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeBits64((uint64_t)mpz_get_lsb(from->i, 64));
}

Value *cast_Integer_to_Int(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeInt((int64_t)mpz_get_lsb(from->i, 64));
}

Value *cast_Integer_to_double(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeDouble(mpz_get_d(from->i));
}

Value *cast_Integer_to_char(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;
    return (Value *)makeChar((unsigned char)mpz_get_lsb(from->i, 8));
}

Value *cast_Integer_to_string(Value *input)
{
    Value_Integer *from = (Value_Integer *)input;

    Value_String *retVal = (Value_String *)newValue();
    retVal->header.tag = STRING_TAG;
    retVal->str = mpz_get_str(NULL, 10, from->i);

    return (Value *)retVal;
}
