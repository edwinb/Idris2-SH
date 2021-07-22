module Data.List.Views.Extra

import Data.List
import Data.List.Reverse
import Data.List.Views
import Data.Nat
import Data.List.Equalities

%default total

||| Proof that two numbers differ by at most one
public export
data Balanced : Nat -> Nat -> Type where
  BalancedZ   : Balanced Z Z
  BalancedL   : Balanced (S Z) Z
  BalancedRec : Balanced n m -> Balanced (S n) (S m)

%name Balanced bal, b

Uninhabited (Balanced Z (S k)) where
  uninhabited BalancedZ impossible
  uninhabited BalancedL impossible
  uninhabited (BalancedRec rec) impossible

export
balancedPred : Balanced (S x) (S y) -> Balanced x y
balancedPred (BalancedRec pred) = pred

export
mkBalancedEq : {n, m : Nat} -> n = m -> Balanced n m
mkBalancedEq {n = 0} Refl = BalancedZ
mkBalancedEq {n = (S k)} Refl = BalancedRec $ mkBalancedEq {n = k} Refl

export
mkBalancedL : {n, m : Nat} -> n = S m -> Balanced n m
mkBalancedL {m = 0} Refl = BalancedL
mkBalancedL {m = S k} Refl = BalancedRec (mkBalancedL Refl)

||| View of a list split into two halves
|||
||| The lengths of the lists are guaranteed to differ by at most one
public export
data SplitBalanced : List a -> Type where
  MkSplitBal
    : {xs, ys : List a}
    -> Balanced (length xs) (length ys)
    -> SplitBalanced (xs ++ ys)

private
splitBalancedHelper
  : (revLs : List a)
  -> (rs : List a)
  -> (doubleSkip : List a)
  -> (length rs = length revLs + length doubleSkip)
  -> SplitBalanced (reverse revLs ++ rs)
splitBalancedHelper revLs rs [] prf = MkSplitBal balancedLeftsAndRights
  where
    lengthsEqual : length rs = length revLs
    lengthsEqual =
      rewrite sym (plusZeroRightNeutral (length revLs)) in prf
    balancedLeftsAndRights : Balanced (length (reverse revLs)) (length rs)
    balancedLeftsAndRights =
      rewrite reverseLength revLs in
        rewrite lengthsEqual in
          mkBalancedEq Refl
splitBalancedHelper revLs [] (x :: xs) prf =
  absurd $
    the (0 = S (plus (length revLs) (length xs))) $
      rewrite plusSuccRightSucc (length revLs) (length xs) in
        prf
splitBalancedHelper revLs (x :: rs) [lastItem] prf =
  rewrite appendAssociative (reverse revLs) [x] rs in
    rewrite sym (reverseCons x revLs) in
      MkSplitBal $
        the (Balanced (length (reverseOnto [x] revLs)) (length rs)) $
          rewrite reverseCons x revLs in
            rewrite lengthSnoc x (reverse revLs) in
              rewrite reverseLength revLs in
                rewrite lengthsEqual in
                  mkBalancedL Refl
  where
    lengthsEqual : length rs = length revLs
    lengthsEqual =
      cong pred $
        the (S (length rs) = S (length revLs)) $
          rewrite plusCommutative 1 (length revLs) in prf
splitBalancedHelper revLs (x :: oneFurther) (_ :: (_ :: twoFurther)) prf =
  rewrite appendAssociative (reverse revLs) [x] oneFurther in
    rewrite sym (reverseCons x revLs) in
      splitBalancedHelper (x :: revLs) oneFurther twoFurther $
        cong pred $
          the (S (length oneFurther) = S (S (plus (length revLs) (length twoFurther)))) $
          rewrite plusSuccRightSucc (length revLs) (length twoFurther) in
            rewrite plusSuccRightSucc (length revLs) (S (length twoFurther)) in
              prf

||| Covering function for the `SplitBalanced`
|||
||| Constructs the view in linear time
export
splitBalanced : (input : List a) -> SplitBalanced input
splitBalanced input = splitBalancedHelper [] input input Refl

||| The `VList` view allows us to recurse on the middle of a list,
||| inspecting the front and back elements simultaneously.
public export
data VList : List a -> Type where
  VNil : VList []
  VOne : VList [x]
  VCons : {x, y : a} -> {xs : List a} -> (rec : Lazy (VList xs)) -> VList (x :: xs ++ [y])

private
toVList
  : (xs : List a)
  -> SnocList ys
  -> Balanced (length xs) (length ys)
  -> VList (xs ++ ys)
toVList [] Empty BalancedZ = VNil
toVList [x] Empty BalancedL = VOne
toVList [] (Snoc x zs rec) prf =
  absurd $
    the (Balanced 0 (S (length zs))) $
      rewrite sym (lengthSnoc x zs) in prf
toVList (x :: xs) (Snoc y ys srec) prf =
  rewrite appendAssociative xs ys [y] in
    VCons $
      toVList xs srec $
        balancedPred $
          rewrite sym (lengthSnoc y ys) in prf

||| Covering function for `VList`
||| Constructs the view in linear time.
export
vList : (xs : List a) -> VList xs
vList xs with (splitBalanced xs)
  vList (ys ++ zs) | (MkSplitBal prf) = toVList ys (snocList zs) prf

||| Lazy filtering of a list based on a predicate.
public export
data LazyFilterRec : List a -> Type where
  Exhausted : (skip : List a) -> LazyFilterRec skip
  Found     : (skip : List a) -- initial non-matching elements
            -> (head : a)      -- first match
            -> Lazy (LazyFilterRec rest)
            -> LazyFilterRec (skip ++ (head :: rest))

||| Covering function for the LazyFilterRec view.
||| Constructs the view lazily in linear time.
total export
lazyFilterRec : (pred : (a -> Bool)) -> (xs : List a) -> LazyFilterRec xs
lazyFilterRec pred [] = Exhausted []
lazyFilterRec pred (x :: xs) with (pred x)
  lazyFilterRec pred (x :: xs) | True = Found [] x (lazyFilterRec pred xs)
  lazyFilterRec pred (x :: []) | False = Exhausted [x]
  lazyFilterRec pred (x :: rest@(_ :: xs)) | False = filterHelper [x] rest
    where
      filterHelper
        : (reverseOfSkipped : List a)
        -> {auto prf1 : NonEmpty reverseOfSkipped}
        -> (rest : List a)
        -> {auto prf2 : NonEmpty rest}
        -> LazyFilterRec (reverse reverseOfSkipped ++ rest)
      filterHelper revSkipped (y :: xs) with (pred y)
        filterHelper revSkipped (y :: xs) | True =
          Found (reverse revSkipped) y (lazyFilterRec pred xs)
        filterHelper revSkipped (y :: []) | False =
          rewrite sym (reverseOntoSpec [y] revSkipped) in
          Exhausted $ reverse (y :: revSkipped)
        filterHelper revSkipped (y :: (z :: zs)) | False =
          rewrite appendAssociative (reverse revSkipped) [y] (z :: zs) in
            rewrite sym (reverseOntoSpec [y] revSkipped) in
              filterHelper (y :: revSkipped) (z :: zs)
