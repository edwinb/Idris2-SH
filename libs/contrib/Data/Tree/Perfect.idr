module Data.Tree.Perfect

import Control.WellFounded
import Decidable.Order.Strict
import Data.Monoid.Exponentiation
import Data.Num.Implementations
import Data.Nat.Views
import Data.Nat
import Data.Nat.Order
import Data.Nat.Order.Strict
import Data.Nat.Order.Properties
import Data.Nat.Exponentiation
import Data.DPair
import Syntax.WithProof
import Syntax.PreorderReasoning.Generic

%default total

public export
data Tree : Nat -> Type -> Type where
  Leaf : a -> Tree Z a
  Node : Tree n a -> Tree n a -> Tree (S n) a

public export
Functor (Tree n) where
  map f (Leaf a) = Leaf (f a)
  map f (Node l r) = Node (map f l) (map f r)

public export
replicate : (n : Nat) -> a -> Tree n a
replicate Z a = Leaf a
replicate (S n) a = let t = replicate n a in Node t t

public export
Apply (Tree n) where
  Leaf f <*> Leaf a = Leaf (f a)
  Node fl fr <*> Node xl xr = Node (fl <*> xl) (fr <*> xr)

public export
{n : _} -> Applicative (Tree n) where
  pure = replicate n

public export
data Path : Nat -> Type where
  Here  : Path Z
  Left  : Path n -> Path (S n)
  Right : Path n -> Path (S n)

public export
toNat : {n : _} -> Path n -> Nat
toNat Here = Z
toNat (Left p) = toNat p
toNat {n = S n} (Right p) = toNat p + pow2 n

export
toNatBounded : (n : Nat) -> (p : Path n) -> toNat p `LT` pow2 n
toNatBounded Z Here = reflexive {rel = LTE}
toNatBounded (S n) (Left p) = CalcWith $
  |~ S (toNat p)
  <~ pow2 n          ...( toNatBounded n p )
  <~ pow2 n + pow2 n ...( lteAddRight (pow2 n) )
  ~~ pow2 (S n)      ...( sym unfoldPow2 )
toNatBounded (S n) (Right p) = CalcWith $
  let ih = toNatBounded n p in
  |~ S (toNat p) + pow2 n
  <~ pow2 n + pow2 n      ...( plusLteMonotoneRight _ _ _ ih )
  ~~ pow2 (S n)           ...( sym unfoldPow2 )

namespace FromNat

  ||| This pattern-matching in `fromNat` is annoying:
  ||| The    `Z (S _)` case is impossible
  ||| In the `k (S n)` case we want to branch on whether `k `LT` pow2 n`
  ||| and get our hands on some proofs.
  ||| This view factors out that work.
  public export
  data View : (k, n : Nat) -> Type where
    ZZ   : View Z Z
    SLT  : (0 p : k `LT` pow2 n) -> View k (S n)
    SNLT : (0 p : k `GTE` pow2 n) ->
           (0 rec : minus k (pow2 n) `LT` pow2 n) -> View k (S n)

  public export
  view : (k, n : Nat) -> (0 _ : k `LT` (pow2 n)) -> View k n
  view Z Z p = ZZ
  view (S _) Z p = void $ absurd (fromLteSucc p)
  view k (S n) p with (@@ lt k (pow2 n))
    view k (S n) p | (True ** eq) = SLT (ltIsLT k (pow2 n) eq)
    view k (S n) p | (False ** eq) = SNLT gte prf where

      0 gte : k `GTE` pow2 n
      gte = notLTImpliesGTE (notltIsNotLT k (pow2 n) eq)

      0 prf : minus k (pow2 n) `LT` pow2 n
      prf = CalcWith $
        |~ S (minus k (pow2 n))
        <~ minus (pow2 (S n)) (pow2 n)
           ...( minusLtMonotone p pow2Increasing )
        ~~ minus (pow2 n + pow2 n) (pow2 n)
           ...( cong (\ m => minus m (pow2 n)) unfoldPow2 )
        ~~ pow2 n
           ...( minusPlus (pow2 n) )

||| Convert a natural number to a path in a perfect binary tree
public export
fromNat : (k, n : Nat) -> (0 _ : k `LT` pow2 n) -> Path n
fromNat k n p with (view k n p)
  fromNat Z Z p | ZZ = Here
  fromNat k (S n) p | SLT lt = Left (fromNat k n lt)
  fromNat k (S n) p | SNLT _ lt = Right (fromNat (minus k (pow2 n)) n lt)

||| The `fromNat` conversion is compatible with the semantics `toNat`
export
fromNatCorrect : (k, n : Nat) -> (0 p : k `LT` pow2 n) ->
                 toNat (fromNat k n p) === k
fromNatCorrect k n p with (view k n p)
  fromNatCorrect Z Z p | ZZ = Refl
  fromNatCorrect k (S n) p | SLT lt = fromNatCorrect k n lt
  fromNatCorrect k (S n) p | SNLT gte lt
     = rewrite fromNatCorrect (minus k (pow2 n)) n lt in
       irrelevantEq $ plusMinusLte (pow2 n) k gte

public export
lookup : Tree n a -> Path n -> a
lookup (Leaf a) Here = a
lookup (Node l _) (Left p) = lookup l p
lookup (Node _ r) (Right p) = lookup r p
