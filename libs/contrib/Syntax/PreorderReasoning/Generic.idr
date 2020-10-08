module Syntax.PreorderReasoning.Generic

import Decidable.Order
infixl 0  ~~
infixl 0  <~
prefix 1  |~
infix  1  ...

public export
data Step : (leq : a -> a -> Type) -> a -> a -> Type where
  (...) : {leq : a -> a -> Type} ->  (y : a) -> x `leq` y -> Step leq x y

public export
data FastDerivation : {leq : a -> a -> Type} -> (x : a) -> (y : a) -> Type where
  (|~) : (x : a) -> FastDerivation x x
  (<~) : {leq : a -> a -> Type} -> {x,y : a} 
         -> FastDerivation {leq = leq} x y -> {z : a} -> (step : Step leq y z) 
         -> FastDerivation {leq = leq} x z

public export  
CalcWith : Preorder dom => {x,y : dom} -> FastDerivation {leq = Order.cmp} x y -> x `cmp` y
CalcWith (|~ x) = reflexive x
CalcWith ((<~) der (z ... step)) = transitive _ _ _ (CalcWith der) step

public export
(~~) : {x,y : dom} 
         -> FastDerivation {leq = leq} x y -> {z : dom} -> (step : Step Equal y z)
         -> FastDerivation {leq = leq} x z
(~~) der (z ... Refl) = der
