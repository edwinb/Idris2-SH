module Control.Applicative.Const

import Data.Contravariant
import Data.Bits

%default total

public export
record Const (a : Type) (b : Type) where
  constructor MkConst
  runConst : a

public export
Eq a => Eq (Const a b) where
  (==) = (==) `on` runConst

public export
Ord a => Ord (Const a b) where
  compare = compare `on` runConst

export
Show a => Show (Const a b) where
  showPrec p (MkConst v) = showCon p "MkConst" (showArg v)

public export
Semigroup a => Semigroup (Const a b) where
  MkConst x <+> MkConst y = MkConst (x <+> y)

public export
Monoid a => Monoid (Const a b) where
  neutral = MkConst neutral

public export
Num a => Num (Const a b) where
  MkConst x + MkConst y = MkConst (x + y)
  MkConst x * MkConst y = MkConst (x * y)
  fromInteger = MkConst . fromInteger

public export
Neg a => Neg (Const a b) where
  negate (MkConst x)    = MkConst (negate x)
  MkConst x - MkConst y = MkConst (x - y)

public export
Abs a => Abs (Const a b) where
  abs (MkConst x)    = MkConst (abs x)

public export
Fractional a => Fractional (Const a b) where
  recip (MkConst x)     = MkConst (recip x)
  MkConst x / MkConst y = MkConst (x / y)

public export
Integral a => Integral (Const a b) where
  MkConst x `div` MkConst y = MkConst (x `div` y)
  MkConst x `mod` MkConst y = MkConst (x `mod` y)

public export
Bits a => Bits (Const a b) where
  Index = Index {a}
  MkConst x .&. MkConst y = MkConst (x .&. y)
  MkConst x .|. MkConst y = MkConst (x .|. y)
  MkConst x `xor` MkConst y = MkConst (x `xor` y)
  shiftL (MkConst v) ix = MkConst (shiftL v ix)
  shiftR (MkConst v) ix = MkConst (shiftR v ix)
  bit = MkConst . bit
  zeroBits = MkConst zeroBits
  complement (MkConst v) = MkConst (complement v)
  oneBits = MkConst oneBits
  complementBit (MkConst v) ix = MkConst (complementBit v ix)
  clearBit (MkConst v) ix = MkConst (clearBit v ix)
  testBit (MkConst v) ix = testBit v ix
  setBit (MkConst v) ix = MkConst (setBit v ix)

public export
FromString a => FromString (Const a b) where
  fromString = MkConst . fromString

public export
Functor (Const a) where
  map _ (MkConst v) = MkConst v

public export
Contravariant (Const a) where
  contramap _ (MkConst v) = MkConst v

public export
Semigroup a => Apply (Const a) where
  MkConst x <*> MkConst y = MkConst (x <+> y)

public export
Monoid a => Applicative (Const a) where
  pure _ = MkConst neutral

public export
Foldable (Const a) where
  foldr _ acc _ = acc
  foldl _ acc _ = acc
  null _ = True
  toList _ = []
  foldMap _ _ = neutral

public export
Traversable (Const a) where
  traverse _ (MkConst v) = pure (MkConst v)

public export
Bifunctor Const where
  bimap f _ (MkConst v) = MkConst (f v)

public export
Bifoldable Const where
  bifoldr f _ acc (MkConst v) = f v acc
  bifoldl f _ acc (MkConst v) = f acc v
  binull _ = False

public export
Bitraversable Const where
  bitraverse f _ (MkConst v) = MkConst <$> f v
