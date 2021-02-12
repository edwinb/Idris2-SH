module Data.Nat.Exponentiation

import Data.Nat as Nat
import Data.Monoid.Exponentiation as Mon
import Data.Num.Implementations as Num
import Data.Nat.Views
import Data.Nat.Order
import Decidable.Order
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic

%default total

public export
pow : Nat -> Nat -> Nat
pow = Mon.(^)

public export
lpow : Nat -> Nat -> Nat
lpow = linear @{Nat.Monoid.Multiplicative}

public export
pow2 : Nat -> Nat
pow2 = (2 ^)

public export
lpow2 : Nat -> Nat
lpow2 = lpow 2

export
modularCorrect : (v : Nat) -> {n : Nat} ->
                 pow v n === lpow v n
modularCorrect
   = Mon.modularCorrect
     @{Nat.Monoid.Multiplicative}
     (sym (multAssociative _ _ _))
     (irrelevantEq $ multOneLeftNeutral _)

export
pow2Correct : {n : Nat} -> pow2 n === lpow2 n
pow2Correct = modularCorrect 2

export
unfoldDouble : {0 n : Nat} -> (2 * n) === (n + n)
unfoldDouble = irrelevantEq $ cong (n +) (plusZeroRightNeutral _)

export
unfoldLpow2 : lpow2 (S n) === (lpow2 n + lpow2 n)
unfoldLpow2 = unfoldDouble

export
unfoldPow2 : pow2 (S n) === (pow2 n + pow2 n)
unfoldPow2 = irrelevantEq $ Calc $
  let mon : Monoid Nat; mon = Nat.Monoid.Multiplicative
      lpow2 : Nat -> Nat; lpow2 = linear @{mon} 2 in
  |~ pow2 (S n)
  ~~ lpow2 (S n)       ...( pow2Correct )
  ~~ lpow2 n + lpow2 n ...( unfoldLpow2 )
  ~~ (pow2 n + pow2 n) ...( cong2 (+) (sym pow2Correct) (sym pow2Correct) )

export
lteLpow2 : {m : Nat} -> 1 `LTE` lpow2 m
lteLpow2 {m = Z} = lteRefl
lteLpow2 {m = S m} = CalcWith $
  let ih = lteLpow2 {m} in
  |~ 1
  <~ 2                 ...( ltZero )
  <~ lpow2 m + lpow2 m ...( plusLteMonotone ih ih )
  ~~ lpow2 (S m)       ...( sym (unfoldLpow2) )

export
ltePow2 : {m : Nat} -> 1 `LTE` pow2 m
ltePow2 = CalcWith $
  |~ 1
  <~ lpow2 m ...( lteLpow2 )
  ~~ pow2 m  ...( sym pow2Correct )

export
pow2Increasing : {m : Nat} -> pow2 m `LT` pow2 (S m)
pow2Increasing = CalcWith $
  |~ S (pow2 m)
  <~ pow2 m + pow2 m ...( plusLteMonotoneRight (pow2 m) 1 (pow2 m) ltePow2 )
  ~~ pow2 (S m)      ...( sym unfoldPow2 )
