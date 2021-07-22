module Decidable.Decidable.Extra

import Data.Rel
import Data.Rel.Complement
import Data.Fun
import Data.Vect
import Data.HVect
import Data.Fun.Extra
import Decidable.Decidable

%default total

public export
NotNot : {n : Nat} -> {ts : Vect n Type} -> (r : Rel ts) -> Rel ts
NotNot r = map @{Nary} (Not . Not) r

[DecidablePartialApplication] {x : t} -> (tts : Decidable (S n) (t :: ts) r) => Decidable n ts (r x) where
  decide = decide @{tts} x

public export
doubleNegationElimination : {n : Nat} -> {0 ts : Vect n Type} -> {r : Rel ts} -> Decidable n ts r =>
  (witness : HVect ts) ->
  uncurry (NotNot {ts} r) witness ->
  uncurry              r  witness
doubleNegationElimination {ts = []} @{dec} [] prfnn =
  case decide @{dec} of
    Yes prf  => prf
    No  prfn => absurd $ prfnn prfn
doubleNegationElimination {ts = t :: ts} @{dec} (w :: witness) prfnn =
  doubleNegationElimination {ts} {r = r w} @{ DecidablePartialApplication @{dec} } witness prfnn

doubleNegationForall : {n : Nat} -> {0 ts : Vect n Type} -> {r : Rel ts} -> Decidable n ts r =>
  All ts (NotNot {ts} r) -> All ts r
doubleNegationForall @{dec} forall_prf =
  let prfnn : (witness : HVect ts) -> uncurry (NotNot {ts} r) witness
      prfnn = uncurryAll forall_prf
      prf   : (witness : HVect ts) -> uncurry              r  witness
      prf witness = doubleNegationElimination @{dec} witness (prfnn witness)
  in curryAll prf

public export
doubleNegationExists : {n : Nat} -> {0 ts : Vect n Type} -> {r : Rel ts} -> Decidable n ts r =>
  Ex ts (NotNot {ts} r) ->
  Ex ts r
doubleNegationExists @{dec} nnxs =
  let witness : HVect ts
      witness = extractWitness nnxs
      witnessingnn : uncurry (NotNot {ts} r) witness
      witnessingnn = extractWitnessCorrect nnxs
      witnessing   : uncurry              r  witness
      witnessing   = doubleNegationElimination @{dec} witness witnessingnn
  in introduceWitness witness witnessing




decideTransform :
  {n : Nat}
  -> {ts : Vect n Type}
  -> {r : Rel ts}
  -> {t : Type -> Type}
  -> (tDec : {a : Type} -> Dec a -> Dec (t a))
  -> (posDec : IsDecidable n ts r)
  -> IsDecidable n ts (chain {ts} t r)
decideTransform tDec posDec =
  curryAll $ \xs =>
    replace {p = id} (chainUncurry (chain t r) Dec xs) $
      replace {p = Dec} (chainUncurry r t xs) $
        tDec $ replace {p = id} (sym $ chainUncurry r Dec xs) $
          uncurryAll posDec xs


||| Convert a decision about a decidable property into one about its negation.
public export
negateDec : (dec : Dec a) -> Dec (Not a)
negateDec (Yes pf) = No ($ pf)
negateDec (No npf) = Yes npf

||| We can turn (Not (Exists Not)) into Forall for decidable types
public export
notExistsNotForall :
  {0 p : a -> Type}
  -> ((x : a) -> Dec (p x))
  -> Dec (x : a ** Not (p x))
  -> Dec ((x : a) -> p x)
notExistsNotForall dec decEx =
  case decEx of
    Yes (x ** nx) => No $ \f => nx $ f x
    No notNot => Yes $ \x => case (dec x) of
      Yes px => px
      No nx => void $ notNot $ (x ** nx)


||| If a relation is decidable, then so is its complement
public export
[DecidableComplement] {n : Nat} -> {ts : Vect n Type} -> {r : Rel ts} -> (posDec : Decidable n ts r) =>
  Decidable n ts (complement {ts} r) where
    decide = decideTransform negateDec (decide @{posDec})
