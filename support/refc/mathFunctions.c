#include "mathFunctions.h"
#include "runtime.h"
#include "memoryManagement.h"

double unpackDouble(Value *d)
{
    return ((Value_Double *)d)->d;
}

/* add */
Value *add_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 + ((Value_Bits8 *)y)->ui8);
}
Value *add_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 + ((Value_Bits16 *)y)->ui16);
}
Value *add_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 + ((Value_Bits32 *)y)->ui32);
}
Value *add_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 + ((Value_Bits64 *)y)->ui64);
}
Value *add_Int8(Value *x, Value *y)
{
    return (Value *)makeInt8(((Value_Int8 *)x)->i8 + ((Value_Int8 *)y)->i8);
}
Value *add_Int16(Value *x, Value *y)
{
    return (Value *)makeInt16(((Value_Int16 *)x)->i16 + ((Value_Int16 *)y)->i16);
}
Value *add_Int32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 + ((Value_Int32 *)y)->i32);
}
Value *add_Int64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 + ((Value_Int64 *)y)->i64);
}
Value *add_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_add(&retVal->i, &((Value_Integer*)x)->i, &((Value_Integer*)y)->i, BF_PREC_INF, 0);
#else
    mpz_add(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#endif
    return (Value *)retVal;
}
Value *add_double(Value *x, Value *y)
{
    return (Value *)makeDouble(((Value_Double *)x)->d + ((Value_Double *)y)->d);
}

/* sub */
Value *sub_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 - ((Value_Bits8 *)y)->ui8);
}
Value *sub_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 - ((Value_Bits16 *)y)->ui16);
}
Value *sub_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 - ((Value_Bits32 *)y)->ui32);
}
Value *sub_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 - ((Value_Bits64 *)y)->ui64);
}
Value *sub_Int8(Value *x, Value *y)
{
    return (Value *)makeInt8(((Value_Int8 *)x)->i8 - ((Value_Int8 *)y)->i8);
}
Value *sub_Int16(Value *x, Value *y)
{
    return (Value *)makeInt16(((Value_Int16 *)x)->i16 - ((Value_Int16 *)y)->i16);
}
Value *sub_Int32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 - ((Value_Int32 *)y)->i32);
}
Value *sub_Int64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 - ((Value_Int64 *)y)->i64);
}
Value *sub_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_sub(&retVal->i, &((Value_Integer*)x)->i, &((Value_Integer*)y)->i, BF_PREC_INF, 0);
#else
    mpz_sub(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#endif
    return (Value *)retVal;
}
Value *sub_double(Value *x, Value *y)
{
    return (Value *)makeDouble(((Value_Double *)x)->d - ((Value_Double *)y)->d);
}

/* negate */
Value *negate_Bits8(Value *x)
{
    return (Value *)makeBits8(-((Value_Bits8 *)x)->ui8);
}
Value *negate_Bits16(Value *x)
{
    return (Value *)makeBits16(-((Value_Bits16 *)x)->ui16);
}
Value *negate_Bits32(Value *x)
{
    return (Value *)makeBits32(-((Value_Bits32 *)x)->ui32);
}
Value *negate_Bits64(Value *x)
{
    return (Value *)makeBits64(-((Value_Bits64 *)x)->ui64);
}
Value *negate_Int8(Value *x)
{
    return (Value *)makeInt8(-((Value_Int8 *)x)->i8);
}
Value *negate_Int16(Value *x)
{
    return (Value *)makeInt16(-((Value_Int16 *)x)->i16);
}
Value *negate_Int32(Value *x)
{
    return (Value *)makeInt32(-((Value_Int32 *)x)->i32);
}
Value *negate_Int64(Value *x)
{
    return (Value *)makeInt64(-((Value_Int64 *)x)->i64);
}
Value *negate_Integer(Value *x)
{
    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_set(&retVal->i, &((Value_Integer*)x)->i);
    bf_neg(&retVal->i);
#else
    mpz_neg(retVal->i, ((Value_Integer *)x)->i);
#endif
    return (Value *)retVal;
}
Value *negate_double(Value *x)
{
    return (Value *)makeDouble(-((Value_Double *)x)->d);
}

/* mul */
Value *mul_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 * ((Value_Bits8 *)y)->ui8);
}
Value *mul_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 * ((Value_Bits16 *)y)->ui16);
}
Value *mul_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 * ((Value_Bits32 *)y)->ui32);
}
Value *mul_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 * ((Value_Bits64 *)y)->ui64);
}
Value *mul_Int8(Value *x, Value *y)
{
    return (Value *)makeInt8(((Value_Int8 *)x)->i8 * ((Value_Int8 *)y)->i8);
}
Value *mul_Int16(Value *x, Value *y)
{
    return (Value *)makeInt16(((Value_Int16 *)x)->i16 * ((Value_Int16 *)y)->i16);
}
Value *mul_Int32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 * ((Value_Int32 *)y)->i32);
}
Value *mul_Int64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 * ((Value_Int64 *)y)->i64);
}
Value *mul_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_mul(&retVal->i, &((Value_Integer*)x)->i, &((Value_Integer*)y)->i, BF_PREC_INF, 0);
#else
    mpz_mul(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#endif
    return (Value *)retVal;
}
Value *mul_double(Value *x, Value *y)
{
    return (Value *)makeDouble(((Value_Double *)x)->d * ((Value_Double *)y)->d);
}

/* div */
Value *div_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 / ((Value_Bits8 *)y)->ui8);
}
Value *div_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 / ((Value_Bits16 *)y)->ui16);
}
Value *div_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 / ((Value_Bits32 *)y)->ui32);
}
Value *div_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 / ((Value_Bits64 *)y)->ui64);
}
Value *div_Int8(Value *x, Value *y)
{
    // Correction term added to convert from truncated division (C default) to Euclidean division
    // For proof of correctness, see Division and Modulus for Computer Scientists (Daan Leijen)
    // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

    int8_t num = ((Value_Int8 *)x)->i8;
    int8_t denom = ((Value_Int8 *)y)->i8;
    int8_t rem = num % denom;
    return (Value *)makeInt8(
        num / denom
        + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0)
    );
}
Value *div_Int16(Value *x, Value *y)
{
    // Correction term added to convert from truncated division (C default) to Euclidean division
    // For proof of correctness, see Division and Modulus for Computer Scientists (Daan Leijen)
    // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

    int16_t num = ((Value_Int16 *)x)->i16;
    int16_t denom = ((Value_Int16 *)y)->i16;
    int16_t rem = num % denom;
    return (Value *)makeInt16(
        num / denom
        + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0)
    );
}
Value *div_Int32(Value *x, Value *y)
{
    // Correction term added to convert from truncated division (C default) to Euclidean division
    // For proof of correctness, see Division and Modulus for Computer Scientists (Daan Leijen)
    // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

    int32_t num = ((Value_Int32 *)x)->i32;
    int32_t denom = ((Value_Int32 *)y)->i32;
    int32_t rem = num % denom;
    return (Value *)makeInt32(
        num / denom
        + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0)
    );
}
Value *div_Int64(Value *x, Value *y)
{
    // Correction term added to convert from truncated division (C default) to Euclidean division
    // For proof of correctness, see Division and Modulus for Computer Scientists (Daan Leijen)
    // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

    int64_t num = ((Value_Int64 *)x)->i64;
    int64_t denom = ((Value_Int64 *)y)->i64;
    int64_t rem = num % denom;
    return (Value *)makeInt64(
        num / denom
        + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0)
    );
}
Value *div_Integer(Value *x, Value *y)
{
    Value_Integer* retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_t r;
    bf_init(((Value_Integer*)x)->i.ctx, &r);
    bf_divrem(&retVal->i, &r, &((Value_Integer*)x)->i, &((Value_Integer*)y)->i, BF_PREC_INF, 0, BF_RNDZ);
#else
    mpz_t rem, yq;
    mpz_inits(rem, yq, NULL);

    mpz_mod(rem, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
    mpz_sub(yq, ((Value_Integer *)x)->i, rem);

    mpz_divexact(retVal->i, yq, ((Value_Integer *)y)->i);

    mpz_clears(rem, yq, NULL);
#endif

    return (Value *)retVal;
}
Value *div_double(Value *x, Value *y)
{
    return (Value *)makeDouble(((Value_Double *)x)->d / ((Value_Double *)y)->d);
}

/* mod */
Value *mod_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 % ((Value_Bits8 *)y)->ui8);
}
Value *mod_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 % ((Value_Bits16 *)y)->ui16);
}
Value *mod_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 % ((Value_Bits32 *)y)->ui32);
}
Value *mod_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 % ((Value_Bits64 *)y)->ui64);
}
Value *mod_Int8(Value *x, Value *y)
{
    int8_t num = ((Value_Int8 *)x)->i8;
    int8_t denom = ((Value_Int8 *)y)->i8;
    denom = (denom < 0) ? - denom : denom;
    return (Value *)makeInt8(num % denom + (num < 0 ? denom : 0));
}
Value *mod_Int16(Value *x, Value *y)
{
    int16_t num = ((Value_Int16 *)x)->i16;
    int16_t denom = ((Value_Int16 *)y)->i16;
    denom = (denom < 0) ? - denom : denom;
    return (Value *)makeInt16(num % denom + (num < 0 ? denom : 0));
}
Value *mod_Int32(Value *x, Value *y)
{
    int32_t num = ((Value_Int32 *)x)->i32;
    int32_t denom = ((Value_Int32 *)y)->i32;
    denom = (denom < 0) ? - denom : denom;
    return (Value *)makeInt32(num % denom + (num < 0 ? denom : 0));
}
Value *mod_Int64(Value *x, Value *y)
{
    int64_t num = ((Value_Int64 *)x)->i64;
    int64_t denom = ((Value_Int64 *)y)->i64;
    denom = (denom < 0) ? - denom : denom;
    return (Value *)makeInt64(num % denom + (num < 0 ? denom : 0));
}
Value *mod_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_rem(&retVal->i, &((Value_Integer*)x)->i, &((Value_Integer*)y)->i, BF_PREC_INF, 0, BF_DIVREM_EUCLIDIAN);
#else
    mpz_mod(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#endif
    return (Value *)retVal;
}

/* shiftl */
Value *shiftl_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 << ((Value_Bits8 *)y)->ui8);
}
Value *shiftl_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 << ((Value_Bits16 *)y)->ui16);
}
Value *shiftl_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 << ((Value_Bits32 *)y)->ui32);
}
Value *shiftl_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 << ((Value_Bits64 *)y)->ui64);
}
Value *shiftl_Int8(Value *x, Value *y)
{
    return (Value *)makeInt8(((Value_Int8 *)x)->i8 << ((Value_Int8 *)y)->i8);
}
Value *shiftl_Int16(Value *x, Value *y)
{
    return (Value *)makeInt16(((Value_Int16 *)x)->i16 << ((Value_Int16 *)y)->i16);
}
Value *shiftl_Int32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 << ((Value_Int32 *)y)->i32);
}
Value *shiftl_Int64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 << ((Value_Int64 *)y)->i64);
}
Value *shiftl_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    int64_t cnt;
    bf_get_int64(&cnt, &((Value_Integer*)y)->i, 0);
    bf_set(&retVal->i, &((Value_Integer*)x)->i);
    bf_mul_2exp(&retVal->i, cnt, BF_PREC_INF, BF_RNDZ);
#else
    mp_bitcnt_t cnt = (mp_bitcnt_t)mpz_get_ui(((Value_Integer *)y)->i);
    mpz_mul_2exp(retVal->i, ((Value_Integer *)x)->i, cnt);
#endif
    return (Value *)retVal;
}

/* shiftr */
Value *shiftr_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 >> ((Value_Bits8 *)y)->ui8);
}
Value *shiftr_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 >> ((Value_Bits16 *)y)->ui16);
}
Value *shiftr_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 >> ((Value_Bits32 *)y)->ui32);
}
Value *shiftr_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 >> ((Value_Bits64 *)y)->ui64);
}
Value *shiftr_Int8(Value *x, Value *y)
{
    return (Value *)makeInt8(((Value_Int8 *)x)->i8 >> ((Value_Int8 *)y)->i8);
}
Value *shiftr_Int16(Value *x, Value *y)
{
    return (Value *)makeInt16(((Value_Int16 *)x)->i16 >> ((Value_Int16 *)y)->i16);
}
Value *shiftr_Int32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 >> ((Value_Int32 *)y)->i32);
}
Value *shiftr_Int64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 >> ((Value_Int64 *)y)->i64);
}
Value *shiftr_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_t e, r;
    int64_t cnt;
    bf_init(retVal->i.ctx, &e);
    bf_init(retVal->i.ctx, &r);
    bf_set_ui(&e, 1);
    bf_get_int64(&cnt, &((Value_Integer*)y)->i, 0);
    bf_mul_2exp(&e, cnt, BF_PREC_INF, BF_RNDZ);
    bf_divrem(&retVal->i, &r, &((Value_Integer*)x)->i, &e, BF_PREC_INF, 0, BF_DIVREM_EUCLIDIAN);
#else
    mp_bitcnt_t cnt = (mp_bitcnt_t)mpz_get_ui(((Value_Integer *)y)->i);
    mpz_fdiv_q_2exp(retVal->i, ((Value_Integer *)x)->i, cnt);
#endif
    return (Value *)retVal;
}

/* and */
Value *and_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 & ((Value_Bits8 *)y)->ui8);
}
Value *and_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 & ((Value_Bits16 *)y)->ui16);
}
Value *and_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 & ((Value_Bits32 *)y)->ui32);
}
Value *and_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 & ((Value_Bits64 *)y)->ui64);
}
Value *and_Int8(Value *x, Value *y)
{
    return (Value *)makeInt8(((Value_Int8 *)x)->i8 & ((Value_Int8 *)y)->i8);
}
Value *and_Int16(Value *x, Value *y)
{
    return (Value *)makeInt16(((Value_Int16 *)x)->i16 & ((Value_Int16 *)y)->i16);
}
Value *and_Int32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 & ((Value_Int32 *)y)->i32);
}
Value *and_Int64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 & ((Value_Int64 *)y)->i64);
}
Value *and_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_logic_and(&retVal->i, &((Value_Integer*)x)->i, &((Value_Integer*)y)->i);
#else
    mpz_and(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#endif
    return (Value *)retVal;
}

/* or */
Value *or_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 | ((Value_Bits8 *)y)->ui8);
}
Value *or_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 | ((Value_Bits16 *)y)->ui16);
}
Value *or_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 | ((Value_Bits32 *)y)->ui32);
}
Value *or_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 | ((Value_Bits64 *)y)->ui64);
}
Value *or_Int8(Value *x, Value *y)
{
    return (Value *)makeInt8(((Value_Int8 *)x)->i8 | ((Value_Int8 *)y)->i8);
}
Value *or_Int16(Value *x, Value *y)
{
    return (Value *)makeInt16(((Value_Int16 *)x)->i16 | ((Value_Int16 *)y)->i16);
}
Value *or_Int32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 | ((Value_Int32 *)y)->i32);
}
Value *or_Int64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 | ((Value_Int64 *)y)->i64);
}
Value *or_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_logic_or(&retVal->i, &((Value_Integer*)x)->i, &((Value_Integer*)y)->i);
#else
    mpz_ior(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#endif
    return (Value *)retVal;
}

/* xor */
Value *xor_Bits8(Value *x, Value *y)
{
    return (Value *)makeBits8(((Value_Bits8 *)x)->ui8 ^ ((Value_Bits8 *)y)->ui8);
}
Value *xor_Bits16(Value *x, Value *y)
{
    return (Value *)makeBits16(((Value_Bits16 *)x)->ui16 ^ ((Value_Bits16 *)y)->ui16);
}
Value *xor_Bits32(Value *x, Value *y)
{
    return (Value *)makeBits32(((Value_Bits32 *)x)->ui32 ^ ((Value_Bits32 *)y)->ui32);
}
Value *xor_Bits64(Value *x, Value *y)
{
    return (Value *)makeBits64(((Value_Bits64 *)x)->ui64 ^ ((Value_Bits64 *)y)->ui64);
}
Value *xor_Int8(Value *x, Value *y)
{
    return (Value *)makeInt8(((Value_Int8 *)x)->i8 ^ ((Value_Int8 *)y)->i8);
}
Value *xor_Int16(Value *x, Value *y)
{
    return (Value *)makeInt16(((Value_Int16 *)x)->i16 ^ ((Value_Int16 *)y)->i16);
}
Value *xor_Int32(Value *x, Value *y)
{
    return (Value *)makeInt32(((Value_Int32 *)x)->i32 ^ ((Value_Int32 *)y)->i32);
}
Value *xor_Int64(Value *x, Value *y)
{
    return (Value *)makeInt64(((Value_Int64 *)x)->i64 ^ ((Value_Int64 *)y)->i64);
}
Value *xor_Integer(Value *x, Value *y)
{
    Value_Integer *retVal = makeInteger();
#ifdef INTEGER_USE_LIBBF
    bf_logic_xor(&retVal->i, &((Value_Integer*)x)->i, &((Value_Integer*)y)->i);
#else
    mpz_xor(retVal->i, ((Value_Integer *)x)->i, ((Value_Integer *)y)->i);
#endif
    return (Value *)retVal;
}

/* lt */
Value *lt_Bits8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits8 *)x)->ui8 < ((Value_Bits8 *)y)->ui8);
}
Value *lt_Bits16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits16 *)x)->ui16 < ((Value_Bits16 *)y)->ui16);
}
Value *lt_Bits32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits32 *)x)->ui32 < ((Value_Bits32 *)y)->ui32);
}
Value *lt_Bits64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits64 *)x)->ui64 < ((Value_Bits64 *)y)->ui64);
}
Value *lt_Int8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int8 *)x)->i8 < ((Value_Int8 *)y)->i8);
}
Value *lt_Int16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int16 *)x)->i16 < ((Value_Int16 *)y)->i16);
}
Value *lt_Int32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int32 *)x)->i32 < ((Value_Int32 *)y)->i32);
}
Value *lt_Int64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int64 *)x)->i64 < ((Value_Int64 *)y)->i64);
}
Value *lt_Integer(Value *x, Value *y)
{
#ifdef INTEGER_USE_LIBBF
    return (Value *)makeBool(
        bf_cmp(&((Value_Integer*)x)->i, &((Value_Integer*)y)->i) < 0
    );
#else
    return (Value *)makeBool(
        mpz_cmp(((Value_Integer *)x)->i, ((Value_Integer *)y)->i) < 0
    );
#endif
}
Value *lt_double(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Double *)x)->d < ((Value_Double *)y)->d);
}
Value *lt_char(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Char *)x)->c < ((Value_Char *)y)->c);
}
Value *lt_string(Value *x, Value *y)
{
    return (Value *)makeBool(strcmp(((Value_String *)x)->str, ((Value_String *)y)->str) < 0);
}

/* gt */
Value *gt_Bits8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits8 *)x)->ui8 > ((Value_Bits8 *)y)->ui8);
}
Value *gt_Bits16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits16 *)x)->ui16 > ((Value_Bits16 *)y)->ui16);
}
Value *gt_Bits32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits32 *)x)->ui32 > ((Value_Bits32 *)y)->ui32);
}
Value *gt_Bits64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits64 *)x)->ui64 > ((Value_Bits64 *)y)->ui64);
}
Value *gt_Int8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int8 *)x)->i8 > ((Value_Int8 *)y)->i8);
}
Value *gt_Int16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int16 *)x)->i16 > ((Value_Int16 *)y)->i16);
}
Value *gt_Int32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int32 *)x)->i32 > ((Value_Int32 *)y)->i32);
}
Value *gt_Int64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int64 *)x)->i64 > ((Value_Int64 *)y)->i64);
}
Value *gt_Integer(Value *x, Value *y)
{
#ifdef INTEGER_USE_LIBBF
    return (Value*)makeBool(
        bf_cmp(&((Value_Integer*)x)->i, &((Value_Integer*)y)->i) > 0
    );
#else
    return (Value *)makeBool(
        mpz_cmp(((Value_Integer *)x)->i, ((Value_Integer *)y)->i) > 0
    );
#endif
}
Value *gt_double(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Double *)x)->d > ((Value_Double *)y)->d);
}
Value *gt_char(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Char *)x)->c > ((Value_Char *)y)->c);
}
Value *gt_string(Value *x, Value *y)
{
    return (Value *)makeBool(strcmp(((Value_String *)x)->str, ((Value_String *)y)->str) > 0);
}

/* eq */
Value *eq_Bits8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits8 *)x)->ui8 == ((Value_Bits8 *)y)->ui8);
}
Value *eq_Bits16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits16 *)x)->ui16 == ((Value_Bits16 *)y)->ui16);
}
Value *eq_Bits32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits32 *)x)->ui32 == ((Value_Bits32 *)y)->ui32);
}
Value *eq_Bits64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits64 *)x)->ui64 == ((Value_Bits64 *)y)->ui64);
}
Value *eq_Int8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int8 *)x)->i8 == ((Value_Int8 *)y)->i8);
}
Value *eq_Int16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int16 *)x)->i16 == ((Value_Int16 *)y)->i16);
}
Value *eq_Int32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int32 *)x)->i32 == ((Value_Int32 *)y)->i32);
}
Value *eq_Int64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int64 *)x)->i64 == ((Value_Int64 *)y)->i64);
}
Value *eq_Integer(Value *x, Value *y)
{
#ifdef INTEGER_USE_LIBBF
    return (Value*)makeBool(
        bf_cmp(&((Value_Integer*)x)->i, &((Value_Integer*)y)->i) == 0
    );
#else
    return (Value *)makeBool(
        mpz_cmp(((Value_Integer *)x)->i, ((Value_Integer *)y)->i) == 0
    );
#endif
}
Value *eq_double(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Double *)x)->d == ((Value_Double *)y)->d);
}
Value *eq_char(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Char *)x)->c == ((Value_Char *)y)->c);
}
Value *eq_string(Value *x, Value *y)
{
    return (Value *)makeBool(!strcmp(((Value_String *)x)->str, ((Value_String *)y)->str));
}

/* lte */
Value *lte_Bits8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits8 *)x)->ui8 <= ((Value_Bits8 *)y)->ui8);
}
Value *lte_Bits16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits16 *)x)->ui16 <= ((Value_Bits16 *)y)->ui16);
}
Value *lte_Bits32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits32 *)x)->ui32 <= ((Value_Bits32 *)y)->ui32);
}
Value *lte_Bits64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits64 *)x)->ui64 <= ((Value_Bits64 *)y)->ui64);
}
Value *lte_Int8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int8 *)x)->i8 <= ((Value_Int8 *)y)->i8);
}
Value *lte_Int16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int16 *)x)->i16 <= ((Value_Int16 *)y)->i16);
}
Value *lte_Int32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int32 *)x)->i32 <= ((Value_Int32 *)y)->i32);
}
Value *lte_Int64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int64 *)x)->i64 <= ((Value_Int64 *)y)->i64);
}
Value *lte_Integer(Value *x, Value *y)
{
#ifdef INTEGER_USE_LIBBF
    return (Value*)makeBool(
        bf_cmp(&((Value_Integer*)x)->i, &((Value_Integer*)y)->i) <= 0
    );
#else
    return (Value *)makeBool(
        mpz_cmp(((Value_Integer *)x)->i, ((Value_Integer *)y)->i) <= 0
    );
#endif
}
Value *lte_double(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Double *)x)->d <= ((Value_Double *)y)->d);
}
Value *lte_char(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Char *)x)->c <= ((Value_Char *)y)->c);
}
Value *lte_string(Value *x, Value *y)
{
    return (Value *)makeBool(strcmp(((Value_String *)x)->str, ((Value_String *)y)->str) <= 0);
}

/* gte */
Value *gte_Bits8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits8 *)x)->ui8 >= ((Value_Bits8 *)y)->ui8);
}
Value *gte_Bits16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits16 *)x)->ui16 >= ((Value_Bits16 *)y)->ui16);
}
Value *gte_Bits32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits32 *)x)->ui32 >= ((Value_Bits32 *)y)->ui32);
}
Value *gte_Bits64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Bits64 *)x)->ui64 >= ((Value_Bits64 *)y)->ui64);
}
Value *gte_Int8(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int8 *)x)->i8 >= ((Value_Int8 *)y)->i8);
}
Value *gte_Int16(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int16 *)x)->i16 >= ((Value_Int16 *)y)->i16);
}
Value *gte_Int32(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int32 *)x)->i32 >= ((Value_Int32 *)y)->i32);
}
Value *gte_Int64(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Int64 *)x)->i64 >= ((Value_Int64 *)y)->i64);
}
Value *gte_Integer(Value *x, Value *y)
{
#ifdef INTEGER_USE_LIBBF
    return (Value*)makeBool(
        bf_cmp(&((Value_Integer*)x)->i, &((Value_Integer*)y)->i) >= 0
    );
#else
    return (Value *)makeBool(
        mpz_cmp(((Value_Integer *)x)->i, ((Value_Integer *)y)->i) >= 0
    );
#endif
}
Value *gte_double(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Double *)x)->d >= ((Value_Double *)y)->d);
}
Value *gte_char(Value *x, Value *y)
{
    return (Value *)makeBool(((Value_Char *)x)->c >= ((Value_Char *)y)->c);
}
Value *gte_string(Value *x, Value *y)
{
    return (Value *)makeBool(strcmp(((Value_String *)x)->str, ((Value_String *)y)->str) >= 0);
}
