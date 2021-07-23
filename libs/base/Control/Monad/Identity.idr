module Control.Monad.Identity

import Data.Bits

%default total

public export
record Identity (a : Type) where
  constructor Id
  runIdentity : a

public export
Functor Identity where
    map fn (Id a) = Id (fn a)

public export
Apply Identity where
    (Id f) <*> (Id g) = Id (f g)

public export
Applicative Identity where
    pure x = Id x

public export
Bind Identity where
    (Id x) >>= k = k x

public export
Monad Identity where

public export
Show a => Show (Identity a) where
  showPrec d (Id x) = showCon d "Id" $ showArg x

public export
Eq a => Eq (Identity a) where
  (Id x) == (Id y) = x == y

public export
Ord a => Ord (Identity a) where
  compare (Id x) (Id y) = compare x y

-- public export
-- Enum a => Enum (Identity a) where
--   toNat (Id x) = toNat x
--   fromNat n = Id $ fromNat n
--   pred (Id n) = Id $ pred n

public export
(Semigroup a) => Semigroup (Identity a) where
  (<+>) x y = Id (runIdentity x <+> runIdentity y)

public export
(Monoid a) => Monoid (Identity a) where
  neutral = Id (neutral)

public export
Num a => Num (Identity a) where
  Id x + Id y = Id (x + y)
  Id x * Id y = Id (x * y)
  fromInteger = Id . fromInteger

public export
Neg a => Neg (Identity a) where
  negate (Id x)    = Id (negate x)
  Id x - Id y = Id (x - y)

public export
Abs a => Abs (Identity a) where
  abs (Id x)    = Id (abs x)

public export
Fractional a => Fractional (Identity a) where
  recip (Id x)     = Id (recip x)
  Id x / Id y = Id (x / y)

public export
Integral a => Integral (Identity a) where
  Id x `div` Id y = Id (x `div` y)
  Id x `mod` Id y = Id (x `mod` y)

public export
Bits a => Bits (Identity a) where
  Index = Index {a}
  Id x .&. Id y = Id (x .&. y)
  Id x .|. Id y = Id (x .|. y)
  Id x `xor` Id y = Id (x `xor` y)
  shiftL (Id v) ix = Id (shiftL v ix)
  shiftR (Id v) ix = Id (shiftR v ix)
  bit = Id . bit
  zeroBits = Id zeroBits
  complement (Id v) = Id (complement v)
  oneBits = Id oneBits
  complementBit (Id v) ix = Id (complementBit v ix)
  clearBit (Id v) ix = Id (clearBit v ix)
  testBit (Id v) ix = testBit v ix
  setBit (Id v) ix = Id (setBit v ix)

public export
FromString a => FromString (Identity a) where
  fromString = Id . fromString
