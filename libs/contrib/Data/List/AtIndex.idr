module Data.List.AtIndex

import Data.DPair
import Data.List.HasLength
import Data.Nat
import Decidable.Equality

%default total

||| @AtIndex witnesses the fact that a natural number encodes a membership proof.
||| It is meant to be used as a runtime-irrelevant gadget to guarantee that the
||| natural number is indeed a valid index.
public export
data AtIndex : a -> List a -> Nat -> Type where
  Z : AtIndex a (a :: as) Z
  S : AtIndex a as n -> AtIndex a (b :: as) (S n)

||| Inversion principle for Z constructor
export
inverseZ : AtIndex x (y :: xs) Z -> x === y
inverseZ Z = Refl

||| inversion principle for S constructor
export
inverseS : AtIndex x (y :: xs) (S n) -> AtIndex x xs n
inverseS (S p) = p

||| An empty list cannot possibly have members
export
Uninhabited (AtIndex a [] n) where
  uninhabited Z impossible
  uninhabited (S _) impossible

||| For a given list and a given index, there is only one possible value
||| stored at that index in that list
export
atIndexUnique : AtIndex a as n -> AtIndex b as n -> a === b
atIndexUnique Z Z = Refl
atIndexUnique (S p) (S q) = atIndexUnique p q

||| Provided that equality is decidable, we can look for the first occurence
||| of a value inside of a list
public export
find : DecEq a => (x : a) -> (xs : List a) -> Dec (Subset Nat (AtIndex x xs))
find x [] = No (\ p => void (absurd (snd p)))
find x (y :: xs) with (decEq x y)
  find x (x :: xs) | Yes Refl = Yes (Element Z Z)
  find x (y :: xs) | No neqxy = case find x xs of
      Yes (Element n prf) => Yes (Element (S n) (S prf))
      No notInxs => No $ \case
        (Element Z p) => void (neqxy (inverseZ p))
        (Element (S n) prf) => absurd (notInxs (Element n (inverseS prf)))

||| If the equality is not decidable, we may instead rely on interface resolution
public export
interface Member (0 t : a) (0 ts : List a) where
  isMember' : Subset Nat (AtIndex t ts)

public export
isMember : (0 t : a) -> (0 ts : List a) -> Member t ts =>
              Subset Nat (AtIndex t ts)
isMember t ts @{p} = isMember' @{p}

public export
Member t (t :: ts) where
  isMember' = Element 0 Z

public export
Member t ts => Member t (u :: ts) where
  isMember' = let (Element n prf) = isMember t ts in
              Element (S n) (S prf)

||| Given an index, we can decide whether there is a value corresponding to it
public export
lookup : (n : Nat) -> (xs : List a) -> Dec (Subset a (\ x => AtIndex x xs n))
lookup n [] = No (\ p => void (absurd (snd p)))
lookup Z (x :: xs) = Yes (Element x Z)
lookup (S n) (x :: xs) = case lookup n xs of
  Yes (Element x p) => Yes (Element x (S p))
  No notInxs => No (\ (Element x p) => void (notInxs (Element x (inverseS p))))

||| An AtIndex proof implies that n is less than the length of the list indexed into
public export
inRange : (n : Nat) -> (xs : List a) -> (0 _ : AtIndex x xs n) -> LTE n (length xs)
inRange n [] p = void (absurd p)
inRange Z (x :: xs) p = LTEZero
inRange (S n) (x :: xs) p = LTESucc (inRange n xs (inverseS p))

|||
export
weakenR : AtIndex x xs n -> AtIndex x (xs ++ ys) n
weakenR Z = Z
weakenR (S p) = S (weakenR p)

export
weakenL : (p : Subset Nat (HasLength ws)) -> AtIndex x xs n -> AtIndex x (ws ++ xs) (fst p + n)
weakenL m p = case view m of
  Z     => p
  (S m) => S (weakenL m p)

export
strengthenL : (p : Subset Nat (HasLength xs)) ->
              lt n (fst p) === True ->
              AtIndex x (xs ++ ys) n -> AtIndex x xs n
strengthenL m lt idx = case view m of
  S m => case idx of
    Z => Z
    S idx => S (strengthenL m lt idx)

export
strengthenR : (p : Subset Nat (HasLength ws)) ->
              lte (fst p) n === True ->
              AtIndex x (ws ++ xs) n -> AtIndex x xs (minus n (fst p))
strengthenR m lt idx = case view m of
  Z => rewrite minusZeroRight n in idx
  S m => case idx of S idx => strengthenR m lt idx
