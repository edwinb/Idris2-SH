module Data.Nat.Equational

import Data.Nat

%default total


||| Subtract a number from both sides of an equation.
||| Due to partial nature of subtraction in natural numbers, an equation of
||| special form is required in order for subtraction to be total.
export
subtractEqLeft : (a : Nat) -> {b, c : Nat} -> a + b = a + c -> b = c
subtractEqLeft 0 prf = prf
subtractEqLeft (S k) prf = subtractEqLeft k $ injective prf

||| Subtract a number from both sides of an equation.
||| Due to partial nature of subtraction in natural numbers, an equation of
||| special form is required in order for subtraction to be total.
export
subtractEqRight : {a, b : Nat} -> (c : Nat) -> a + c = b + c -> a = b
subtractEqRight c prf =
    subtractEqLeft c $
    rewrite plusCommutative c a in
    rewrite plusCommutative c b in
    prf

||| Add a number to both sides of an inequality
export
plusLteLeft : (a : Nat) -> {b, c : Nat} -> LTE b c -> LTE (a + b) (a + c)
plusLteLeft 0 bLTEc = bLTEc
plusLteLeft (S k) bLTEc = LTESucc $ plusLteLeft k bLTEc

||| Add a number to both sides of an inequality
export
plusLteRight : {a, b : Nat} -> (c : Nat) -> LTE a b -> LTE (a + c) (b + c)
plusLteRight c aLTEb =
    rewrite plusCommutative a c in
    rewrite plusCommutative b c in
    plusLteLeft c aLTEb

||| Only 0 is lte 0
||| Useful when the argument is an open term
export
lteZeroIsZero : a `LTE` 0 -> a = 0
lteZeroIsZero LTEZero = Refl

||| Subtract a number from both sides of an inequality.
||| Due to partial nature of subtraction, we require an inequality of special form.
export
subtractLteLeft : (a : Nat) -> {b, c : Nat} -> LTE (a + b) (a + c) -> LTE b c
subtractLteLeft 0 abLTEac = abLTEac
subtractLteLeft (S k) abLTEac = subtractLteLeft k $ fromLteSucc abLTEac

||| Subtract a number from both sides of an inequality.
||| Due to partial nature of subtraction, we require an inequality of special form.
export
subtractLteRight : {a, b : Nat} -> (c : Nat) -> LTE (a + c) (b + c) -> LTE a b
subtractLteRight c acLTEbc =
    subtractLteLeft c $
    rewrite plusCommutative c a in
    rewrite plusCommutative c b in
    acLTEbc

||| If one of the factors of a product is greater than 0, then the other factor
||| is less than or equal to the product..
export
rightFactorLteProduct : (a, b : Nat) -> LTE b (S a * b)
rightFactorLteProduct a b = lteAddRight b

||| If one of the factors of a product is greater than 0, then the other factor
||| is less than or equal to the product..
export
leftFactorLteProduct : (a, b : Nat) -> LTE a (a * S b)
leftFactorLteProduct a b =
    rewrite multRightSuccPlus a b in
    lteAddRight a
