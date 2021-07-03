module Data.Nat

import public Control.Relation
import public Control.Order
import public Control.Function

%default total

export
Uninhabited (Z = S n) where
  uninhabited Refl impossible

export
Uninhabited (S n = Z) where
  uninhabited Refl impossible

export
Uninhabited (a = b) => Uninhabited (S a = S b) where
  uninhabited Refl @{ab} = uninhabited @{ab} Refl

public export
isZero : Nat -> Bool
isZero Z     = True
isZero (S n) = False

public export
isSucc : Nat -> Bool
isSucc Z     = False
isSucc (S n) = True

public export
data IsSucc : (n : Nat) -> Type where
  ItIsSucc : IsSucc (S n)

export
Uninhabited (IsSucc Z) where
  uninhabited ItIsSucc impossible

public export
isItSucc : (n : Nat) -> Dec (IsSucc n)
isItSucc Z = No absurd
isItSucc (S n) = Yes ItIsSucc

public export
power : Nat -> Nat -> Nat
power base Z       = S Z
power base (S exp) = base * (power base exp)

public export
hyper : Nat -> Nat -> Nat -> Nat
hyper Z        a b      = S b
hyper (S Z)    a Z      = a
hyper (S(S Z)) a Z      = Z
hyper n        a Z      = S Z
hyper (S pn)   a (S pb) = hyper pn a (hyper (S pn) a pb)

public export
pred : Nat -> Nat
pred Z     = Z
pred (S n) = n

-- Comparisons

public export
data NotBothZero : (n, m : Nat) -> Type where
  LeftIsNotZero  : NotBothZero (S n) m
  RightIsNotZero : NotBothZero n     (S m)

export
Uninhabited (NotBothZero 0 0) where
  uninhabited LeftIsNotZero impossible
  uninhabited RightIsNotZero impossible

public export
data LTE  : (n, m : Nat) -> Type where
  LTEZero : LTE Z    right
  LTESucc : LTE left right -> LTE (S left) (S right)

export
Uninhabited (LTE (S n) Z) where
  uninhabited LTEZero impossible

export
Uninhabited (LTE m n) => Uninhabited (LTE (S m) (S n)) where
  uninhabited (LTESucc lte) = uninhabited lte

public export
Reflexive Nat LTE where
  reflexive {x = Z} = LTEZero
  reflexive {x = S k} = LTESucc $ reflexive {x = k}

public export
Transitive Nat LTE where
  transitive LTEZero _ = LTEZero
  transitive (LTESucc xy) (LTESucc yz) =
    LTESucc $ transitive {rel = LTE} xy yz

public export
Antisymmetric Nat LTE where
  antisymmetric LTEZero LTEZero = Refl
  antisymmetric (LTESucc xy) (LTESucc yx) =
    cong S $ antisymmetric xy yx

public export
Connex Nat LTE where
  connex {x = Z} _ = Left LTEZero
  connex {y = Z} _ = Right LTEZero
  connex {x = S _} {y = S _} prf =
    case connex {rel = LTE} $ prf . (cong S) of
      Left jk => Left $ LTESucc jk
      Right kj => Right $ LTESucc kj

public export
Preorder Nat LTE where

public export
PartialOrder Nat LTE where

public export
LinearOrder Nat LTE where

public export
GTE : Nat -> Nat -> Type
GTE left right = LTE right left

public export
LT : Nat -> Nat -> Type
LT left right = LTE (S left) right

namespace LT

  ||| LT is defined in terms of LTE which makes it annoying to use.
  ||| This convenient view of allows us to avoid having to constantly
  ||| perform nested matches to obtain another LT subproof instead of
  ||| an LTE one.
  public export
  data View : LT m n -> Type where
    LTZero : View (LTESucc LTEZero)
    LTSucc : (lt : m `LT` n) -> View (LTESucc lt)

  ||| Deconstruct an LT proof into either a base case or a further *LT*
  export
  view : (lt : LT m n) -> View lt
  view (LTESucc LTEZero) = LTZero
  view (LTESucc lt@(LTESucc _)) = LTSucc lt

  ||| A convenient alias for trivial LT proofs
  export
  ltZero : Z `LT` S m
  ltZero = LTESucc LTEZero

public export
GT : Nat -> Nat -> Type
GT left right = LT right left

export
succNotLTEzero : Not (LTE (S m) Z)
succNotLTEzero LTEZero impossible

export
fromLteSucc : LTE (S m) (S n) -> LTE m n
fromLteSucc (LTESucc x) = x

export
succNotLTEpred : {x : Nat} -> Not $ LTE (S x) x
succNotLTEpred {x =   0} prf = succNotLTEzero prf
succNotLTEpred {x = S _} prf = succNotLTEpred $ fromLteSucc prf

public export
isLTE : (m, n : Nat) -> Dec (LTE m n)
isLTE Z n = Yes LTEZero
isLTE (S k) Z = No succNotLTEzero
isLTE (S k) (S j)
    = case isLTE k j of
           No contra => No (contra . fromLteSucc)
           Yes prf => Yes (LTESucc prf)

public export
isGTE : (m, n : Nat) -> Dec (GTE m n)
isGTE m n = isLTE n m

public export
isLT : (m, n : Nat) -> Dec (LT m n)
isLT m n = isLTE (S m) n

public export
isGT : (m, n : Nat) -> Dec (GT m n)
isGT m n = isLT n m

export
lteSuccRight : LTE n m -> LTE n (S m)
lteSuccRight LTEZero     = LTEZero
lteSuccRight (LTESucc x) = LTESucc (lteSuccRight x)

export
lteSuccLeft : LTE (S n) m -> LTE n m
lteSuccLeft (LTESucc x) = lteSuccRight x

export
lteAddRight : (n : Nat) -> LTE n (n + m)
lteAddRight Z = LTEZero
lteAddRight (S k) {m} = LTESucc (lteAddRight {m} k)

export
notLTEImpliesGT : {a, b : Nat} -> Not (a `LTE` b) -> a `GT` b
notLTEImpliesGT {a = 0  }           not_z_lte_b    = absurd $ not_z_lte_b LTEZero
notLTEImpliesGT {a = S a} {b = 0  } notLTE = LTESucc LTEZero
notLTEImpliesGT {a = S a} {b = S k} notLTE = LTESucc (notLTEImpliesGT (notLTE . LTESucc))

export
LTEImpliesNotGT : a `LTE` b -> Not (a `GT` b)
LTEImpliesNotGT LTEZero q = absurd q
LTEImpliesNotGT (LTESucc p) (LTESucc q) = LTEImpliesNotGT p q

export
notLTImpliesGTE : {a, b : _} -> Not (LT a b) -> GTE a b
notLTImpliesGTE notLT = fromLteSucc $ notLTEImpliesGT notLT

export
LTImpliesNotGTE : a `LT` b -> Not (a `GTE` b)
LTImpliesNotGTE p q = LTEImpliesNotGT q p

public export
lte : Nat -> Nat -> Bool
lte Z        right     = True
lte left     Z         = False
lte (S left) (S right) = lte left right

public export
gte : Nat -> Nat -> Bool
gte left right = lte right left

public export
lt : Nat -> Nat -> Bool
lt left right = lte (S left) right

public export
gt : Nat -> Nat -> Bool
gt left right = lt right left

export
lteReflectsLTE : (k : Nat) -> (n : Nat) -> lte k n === True -> k `LTE` n
lteReflectsLTE (S k)  0    _ impossible
lteReflectsLTE 0      0    _   = LTEZero
lteReflectsLTE 0     (S k) _   = LTEZero
lteReflectsLTE (S k) (S j) prf = LTESucc (lteReflectsLTE k j prf)

export
gteReflectsGTE : (k : Nat) -> (n : Nat) -> gte k n === True -> k `GTE` n
gteReflectsGTE k n prf = lteReflectsLTE n k prf

export
ltReflectsLT : (k : Nat) -> (n : Nat) -> lt k n === True -> k `LT` n
ltReflectsLT k n prf = lteReflectsLTE (S k) n prf

export
gtReflectsGT : (k : Nat) -> (n : Nat) -> gt k n === True -> k `GT` n
gtReflectsGT k n prf = ltReflectsLT n k prf

public export
minimum : Nat -> Nat -> Nat
minimum Z m = Z
minimum (S n) Z = Z
minimum (S n) (S m) = S (minimum n m)

public export
maximum : Nat -> Nat -> Nat
maximum Z m = m
maximum (S n) Z = S n
maximum (S n) (S m) = S (maximum n m)

-- Proofs on S

export
eqSucc : (0 left, right : Nat) -> left = right -> S left = S right
eqSucc _ _ Refl = Refl

export
Injective S where
  injective Refl = Refl

||| A definition of non-zero with a better behaviour than `Not (x = Z)`
||| This is amenable to proof search and `NonZero Z` is more readily
||| detected as impossible by Idris
public export
data NonZero : Nat -> Type where
  SIsNonZero : NonZero (S x)

export Uninhabited (NonZero Z) where uninhabited SIsNonZero impossible

export
SIsNotZ : Not (S x = Z)
SIsNotZ = absurd

||| Auxiliary function:
||| mod' fuel a b = a `mod` (S b)
||| assuming we have enough fuel
public export
mod' : Nat -> Nat -> Nat -> Nat
mod' Z        centre right = centre
mod' (S fuel) centre right =
      if lte centre right then
        centre
      else
        mod' fuel (minus centre (S right)) right

public export
modNatNZ : Nat -> (y: Nat) -> (0 _ : NonZero y) -> Nat
modNatNZ left Z         p = void (absurd p)
modNatNZ left (S right) _ = mod' left left right

export partial
modNat : Nat -> Nat -> Nat
modNat left (S right) = modNatNZ left (S right) SIsNonZero

||| Auxiliary function:
||| div' fuel a b = a `div` (S b)
||| assuming we have enough fuel
public export
div' : Nat -> Nat -> Nat -> Nat
div' Z        centre right = Z
div' (S fuel) centre right =
  if lte centre right then
    Z
  else
    S (div' fuel (minus centre (S right)) right)

-- 'public' to allow type-level division
public export
divNatNZ : Nat -> (y: Nat) -> (0 _ : NonZero y) -> Nat
divNatNZ left (S right) _ = div' left left right

export partial
divNat : Nat -> Nat -> Nat
divNat left (S right) = divNatNZ left (S right) SIsNonZero

export partial
divCeilNZ : Nat -> (y: Nat) -> (0 _ : NonZero y) -> Nat
divCeilNZ x y p = case (modNatNZ x y p) of
  Z   => divNatNZ x y p
  S _ => S (divNatNZ x y p)

export partial
divCeil : Nat -> Nat -> Nat
divCeil x (S y) = divCeilNZ x (S y) SIsNonZero


public export
divmod' : Nat -> Nat -> Nat -> (Nat, Nat)
divmod' Z        centre right = (Z, centre)
divmod' (S fuel) centre right =
  if lte centre right then
    (Z, centre)
  else
    let qr = divmod' fuel (minus centre (S right)) right
    in (S (fst qr), snd qr)

public export
divmodNatNZ : Nat -> (y: Nat) -> (0 _ : NonZero y) -> (Nat, Nat)
divmodNatNZ left (S right) _ = divmod' left left right


public export
Integral Nat where
  div = divNat
  mod = modNat

export partial
gcd : (a: Nat) -> (b: Nat) -> {auto ok: NotBothZero a b} -> Nat
gcd a Z     = a
gcd Z b     = b
gcd a (S b) = gcd (S b) (modNatNZ a (S b) SIsNonZero)

export partial
lcm : Nat -> Nat -> Nat
lcm _ Z     = Z
lcm Z _     = Z
lcm a (S b) = divNat (a * (S b)) (gcd a (S b))

--------------------------------------------------------------------------------
-- An informative comparison view
--------------------------------------------------------------------------------
public export
data CmpNat : Nat -> Nat -> Type where
     CmpLT : (y : _) -> CmpNat x (x + S y)
     CmpEQ : CmpNat x x
     CmpGT : (x : _) -> CmpNat (y + S x) y

export
cmp : (x, y : Nat) -> CmpNat x y
cmp Z Z     = CmpEQ
cmp Z (S k) = CmpLT _
cmp (S k) Z = CmpGT _
cmp (S x) (S y) with (cmp x y)
  cmp (S x) (S (x + (S k))) | CmpLT k = CmpLT k
  cmp (S x) (S x)           | CmpEQ   = CmpEQ
  cmp (S (y + (S k))) (S y) | CmpGT k = CmpGT k

-- Proofs on +

export
plusZeroLeftNeutral : (right : Nat) -> 0 + right = right
plusZeroLeftNeutral _ = Refl

export
plusZeroRightNeutral : (left : Nat) -> left + 0 = left
plusZeroRightNeutral Z     = Refl
plusZeroRightNeutral (S n) = rewrite plusZeroRightNeutral n in Refl

export
plusSuccRightSucc : (left, right : Nat) -> S (left + right) = left + (S right)
plusSuccRightSucc Z _ = Refl
plusSuccRightSucc (S left) right = rewrite plusSuccRightSucc left right in Refl

export
plusCommutative : (left, right : Nat) -> left + right = right + left
plusCommutative Z right = rewrite plusZeroRightNeutral right in Refl
plusCommutative (S left) right =
  rewrite plusCommutative left right in
    rewrite plusSuccRightSucc right left in
      Refl

export
plusAssociative : (left, centre, right : Nat) ->
  left + (centre + right) = (left + centre) + right
plusAssociative Z _ _ = Refl
plusAssociative (S left) centre right =
    rewrite plusAssociative left centre right in Refl

export
plusConstantRight : (left, right, c : Nat) -> left = right ->
  left + c = right + c
plusConstantRight _ _ _ Refl = Refl

export
plusConstantLeft : (left, right, c : Nat) -> left = right ->
  c + left = c + right
plusConstantLeft _ _ _ Refl = Refl

export
plusOneSucc : (right : Nat) -> 1 + right = S right
plusOneSucc _ = Refl

export
plusLeftCancel : (left, right, right' : Nat) ->
  left + right = left + right' -> right = right'
plusLeftCancel Z _ _ p = p
plusLeftCancel (S left) right right' p =
    plusLeftCancel left right right' $ injective p

export
plusRightCancel : (left, left', right : Nat) ->
  left + right = left' + right -> left = left'
plusRightCancel left left' right p =
  plusLeftCancel right left left' $
    rewrite plusCommutative right left in
      rewrite plusCommutative right left' in
        p

export
plusLeftLeftRightZero : (left, right : Nat) ->
  left + right = left -> right = Z
plusLeftLeftRightZero left right p =
  plusLeftCancel left right Z $
    rewrite plusZeroRightNeutral left in
      p

export
plusLteMonotoneRight : (p, q, r : Nat) -> q `LTE` r -> (q+p) `LTE` (r+p)
plusLteMonotoneRight p  Z     r     LTEZero    = rewrite plusCommutative r p in
                                                 lteAddRight p
plusLteMonotoneRight p (S q) (S r) (LTESucc l) = LTESucc $ plusLteMonotoneRight p q r l

export
plusLteMonotoneLeft : (p, q, r : Nat) -> q `LTE` r -> (p + q) `LTE` (p + r)
plusLteMonotoneLeft p q r p_lt_q
   = rewrite plusCommutative p q in
     rewrite plusCommutative p r in
     plusLteMonotoneRight p q r p_lt_q

export
plusLteMonotone : {m, n, p, q : Nat} -> m `LTE` n -> p `LTE` q ->
                  (m + p) `LTE` (n + q)
plusLteMonotone left right =
  transitive {rel=LTE}
    (plusLteMonotoneLeft m p q right)
    (plusLteMonotoneRight q m n left)

zeroPlusLeftZero : (a,b : Nat) -> (0 = a + b) -> a = 0
zeroPlusLeftZero 0 0 Refl = Refl
zeroPlusLeftZero (S k) b _ impossible

zeroPlusRightZero : (a,b : Nat) -> (0 = a + b) -> b = 0
zeroPlusRightZero 0 0 Refl = Refl
zeroPlusRightZero (S k) b _ impossible

-- Proofs on *

export
multZeroLeftZero : (right : Nat) -> Z * right = Z
multZeroLeftZero _ = Refl

export
multZeroRightZero : (left : Nat) -> left * Z = Z
multZeroRightZero Z        = Refl
multZeroRightZero (S left) = multZeroRightZero left

export
multRightSuccPlus : (left, right : Nat) ->
  left * (S right) = left + (left * right)
multRightSuccPlus Z _ = Refl
multRightSuccPlus (S left) right =
  rewrite multRightSuccPlus left right in
  rewrite plusAssociative left right (left * right) in
  rewrite plusAssociative right left (left * right) in
  rewrite plusCommutative right left in
          Refl

export
multLeftSuccPlus : (left, right : Nat) ->
  (S left) * right = right + (left * right)
multLeftSuccPlus _ _ = Refl

export
multCommutative : (left, right : Nat) -> left * right = right * left
multCommutative Z right = rewrite multZeroRightZero right in Refl
multCommutative (S left) right =
  rewrite multCommutative left right in
  rewrite multRightSuccPlus right left in
          Refl

export
multDistributesOverPlusLeft : (left, centre, right : Nat) ->
  (left + centre) * right = (left * right) + (centre * right)
multDistributesOverPlusLeft Z _ _ = Refl
multDistributesOverPlusLeft (S k) centre right =
  rewrite multDistributesOverPlusLeft k centre right in
    rewrite plusAssociative right (k * right) (centre * right) in
      Refl

export
multDistributesOverPlusRight : (left, centre, right : Nat) ->
  left * (centre + right) = (left * centre) + (left * right)
multDistributesOverPlusRight left centre right =
  rewrite multCommutative left (centre + right) in
    rewrite multCommutative left centre in
      rewrite multCommutative left right in
  multDistributesOverPlusLeft centre right left

export
multAssociative : (left, centre, right : Nat) ->
  left * (centre * right) = (left * centre) * right
multAssociative Z _ _ = Refl
multAssociative (S left) centre right =
  rewrite multAssociative left centre right in
    rewrite multDistributesOverPlusLeft centre (mult left centre) right in
      Refl

export
multOneLeftNeutral : (right : Nat) -> 1 * right = right
multOneLeftNeutral right = plusZeroRightNeutral right

export
multOneRightNeutral : (left : Nat) -> left * 1 = left
multOneRightNeutral left =
  rewrite multCommutative left 1 in
  multOneLeftNeutral left

-- Proofs on minus

export
minusSuccSucc : (left, right : Nat) ->
  minus (S left) (S right) = minus left right
minusSuccSucc _ _ = Refl

export
minusZeroLeft : (right : Nat) -> minus 0 right = Z
minusZeroLeft _ = Refl

export
minusZeroRight : (left : Nat) -> minus left 0 = left
minusZeroRight Z     = Refl
minusZeroRight (S _) = Refl

export
minusZeroN : (n : Nat) -> Z = minus n n
minusZeroN Z     = Refl
minusZeroN (S n) = minusZeroN n

export
minusOneSuccN : (n : Nat) -> S Z = minus (S n) n
minusOneSuccN Z     = Refl
minusOneSuccN (S n) = minusOneSuccN n

export
minusSuccOne : (n : Nat) -> minus (S n) 1 = n
minusSuccOne Z     = Refl
minusSuccOne (S _) = Refl

export
minusPlusZero : (n, m : Nat) -> minus n (n + m) = Z
minusPlusZero Z     _ = Refl
minusPlusZero (S n) m = minusPlusZero n m

export
minusPos : m `LT` n -> Z `LT` minus n m
minusPos lt = case view lt of
  LTZero    => ltZero
  LTSucc lt => minusPos lt

export
minusLteMonotone : {p : Nat} -> m `LTE` n -> minus m p `LTE` minus n p
minusLteMonotone LTEZero = LTEZero
minusLteMonotone {p = Z} prf@(LTESucc _) = prf
minusLteMonotone {p = S p} (LTESucc lte) = minusLteMonotone lte

export
minusLtMonotone : m `LT` n -> p `LT` n -> minus m p `LT` minus n p
minusLtMonotone mltn pltn = case view pltn of
  LTZero => rewrite minusZeroRight m in mltn
  LTSucc pltn => case view mltn of
    LTZero => minusPos pltn
    LTSucc mltn => minusLtMonotone mltn pltn

public export
minusPlus : (m : Nat) -> minus (plus m n) m === n
minusPlus Z = irrelevantEq (minusZeroRight n)
minusPlus (S m) = minusPlus m

export
plusMinusLte : (n, m : Nat) -> LTE n m -> (minus m n) + n = m
plusMinusLte  Z     m    _   = rewrite minusZeroRight m in
                               plusZeroRightNeutral m
plusMinusLte (S _)  Z    lte = absurd lte
plusMinusLte (S n) (S m) lte = rewrite sym $ plusSuccRightSucc (minus m n) n in
                               cong S $ plusMinusLte n m (fromLteSucc lte)

export
minusMinusMinusPlus : (left, centre, right : Nat) ->
  minus (minus left centre) right = minus left (centre + right)
minusMinusMinusPlus Z Z _ = Refl
minusMinusMinusPlus (S _) Z _ = Refl
minusMinusMinusPlus Z (S _) _ = Refl
minusMinusMinusPlus (S left) (S centre) right =
  rewrite minusMinusMinusPlus left centre right in Refl

export
plusMinusLeftCancel : (left, right : Nat) -> (right' : Nat) ->
  minus (left + right) (left + right') = minus right right'
plusMinusLeftCancel Z _ _ = Refl
plusMinusLeftCancel (S left) right right' =
  rewrite plusMinusLeftCancel left right right' in Refl

export
multDistributesOverMinusLeft : (left, centre, right : Nat) ->
  (minus left centre) * right = minus (left * right) (centre * right)
multDistributesOverMinusLeft Z Z _ = Refl
multDistributesOverMinusLeft (S left) Z right =
  rewrite minusZeroRight (right + (left * right)) in Refl
multDistributesOverMinusLeft Z (S _) _ = Refl
multDistributesOverMinusLeft (S left) (S centre) right =
  rewrite multDistributesOverMinusLeft left centre right in
  rewrite plusMinusLeftCancel right (left * right) (centre * right) in
          Refl

export
multDistributesOverMinusRight : (left, centre, right : Nat) ->
  left * (minus centre right) = minus (left * centre) (left * right)
multDistributesOverMinusRight left centre right =
    rewrite multCommutative left (minus centre right) in
    rewrite multDistributesOverMinusLeft centre right left in
    rewrite multCommutative centre left in
    rewrite multCommutative right left in
            Refl

export
zeroMultEitherZero : (a,b : Nat) -> a*b = 0 -> Either (a = 0) (b = 0)
zeroMultEitherZero 0 b prf = Left Refl
zeroMultEitherZero (S a) b prf = Right $ zeroPlusLeftZero b (a * b) (sym prf)

-- power proofs

-- multPowerPowerPlus : (base, exp, exp' : Nat) ->
--   power base (exp + exp') = (power base exp) * (power base exp')
-- multPowerPowerPlus base Z       exp' =
--     rewrite sym $ plusZeroRightNeutral (power base exp') in Refl
-- multPowerPowerPlus base (S exp) exp' =
--   rewrite multPowerPowerPlus base exp exp' in
--     rewrite sym $ multAssociative base (power base exp) (power base exp') in
--       Refl

--powerOneNeutral : (base : Nat) -> power base 1 = base
--powerOneNeutral base = rewrite multCommutative base 1 in multOneLeftNeutral base
--
--powerOneSuccOne : (exp : Nat) -> power 1 exp = 1
--powerOneSuccOne Z       = Refl
--powerOneSuccOne (S exp) = rewrite powerOneSuccOne exp in Refl
--
--powerPowerMultPower : (base, exp, exp' : Nat) ->
--  power (power base exp) exp' = power base (exp * exp')
--powerPowerMultPower _ exp Z = rewrite multZeroRightZero exp in Refl
--powerPowerMultPower base exp (S exp') =
--  rewrite powerPowerMultPower base exp exp' in
--  rewrite multRightSuccPlus exp exp' in
--  rewrite sym $ multPowerPowerPlus base exp (exp * exp') in
--          Refl

-- minimum / maximum proofs

export
maximumAssociative : (l, c, r : Nat) ->
  maximum l (maximum c r) = maximum (maximum l c) r
maximumAssociative Z _ _ = Refl
maximumAssociative (S _) Z _ = Refl
maximumAssociative (S _) (S _) Z = Refl
maximumAssociative (S k) (S j) (S i) = rewrite maximumAssociative k j i in Refl

export
maximumCommutative : (l, r : Nat) -> maximum l r = maximum r l
maximumCommutative Z Z = Refl
maximumCommutative Z (S _) = Refl
maximumCommutative (S _) Z = Refl
maximumCommutative (S k) (S j) = rewrite maximumCommutative k j in Refl

export
maximumIdempotent : (n : Nat) -> maximum n n = n
maximumIdempotent Z = Refl
maximumIdempotent (S k) = cong S $ maximumIdempotent k

export
minimumAssociative : (l, c, r : Nat) ->
  minimum l (minimum c r) = minimum (minimum l c) r
minimumAssociative Z _ _ = Refl
minimumAssociative (S _) Z _ = Refl
minimumAssociative (S _) (S _) Z = Refl
minimumAssociative (S k) (S j) (S i) = rewrite minimumAssociative k j i in Refl

export
minimumCommutative : (l, r : Nat) -> minimum l r = minimum r l
minimumCommutative Z Z = Refl
minimumCommutative Z (S _) = Refl
minimumCommutative (S _) Z = Refl
minimumCommutative (S k) (S j) = rewrite minimumCommutative k j in Refl

export
minimumIdempotent : (n : Nat) -> minimum n n = n
minimumIdempotent Z = Refl
minimumIdempotent (S k) = cong S $ minimumIdempotent k

export
minimumZeroZeroLeft : (left : Nat) -> minimum left 0 = Z
minimumZeroZeroLeft left = rewrite minimumCommutative left 0 in Refl

export
minimumSuccSucc : (left, right : Nat) ->
  minimum (S left) (S right) = S (minimum left right)
minimumSuccSucc _ _ = Refl

export
maximumZeroNLeft : (left : Nat) -> maximum left Z = left
maximumZeroNLeft left = rewrite maximumCommutative left Z in Refl

export
maximumSuccSucc : (left, right : Nat) ->
  S (maximum left right) = maximum (S left) (S right)
maximumSuccSucc _ _ = Refl

export
sucMaxL : (l : Nat) -> maximum (S l) l = (S l)
sucMaxL Z = Refl
sucMaxL (S l) = cong S $ sucMaxL l

export
sucMaxR : (l : Nat) -> maximum l (S l) = (S l)
sucMaxR Z = Refl
sucMaxR (S l) = cong S $ sucMaxR l

export
sucMinL : (l : Nat) -> minimum (S l) l = l
sucMinL Z = Refl
sucMinL (S l) = cong S $ sucMinL l

export
sucMinR : (l : Nat) -> minimum l (S l) = l
sucMinR Z = Refl
sucMinR (S l) = cong S $ sucMinR l

-- Algebra -----------------------------

namespace Semigroup

  public export
  [Maximum] Semigroup Nat where
    (<+>) = max

  public export
  [Minimum] Semigroup Nat where
    (<+>) = min

namespace Monoid

  public export
  [Maximum] Monoid Nat using Semigroup.Maximum where
    neutral = 0
