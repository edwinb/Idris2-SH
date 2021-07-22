||| Division theorem for (type-level) natural number division
module Data.Nat.Division

import Syntax.WithProof
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic
import Data.Nat
import Data.Nat.Equational
import Data.Nat.Order
import Data.Nat.Order.Strict
import Data.Nat.Order.Properties
import Decidable.Order.Strict

import Data.Nat.Properties

%default total

-- Division theorem --------------------

-- This is disgusting, but will do for now
||| Show that, if we have enough fuel, we have enough fuel for the
||| recursive call in `div'` and `mod'`.
fuelLemma : (numer, predDenom, fuel : Nat)
          -> (enough : numer `LTE` (S fuel))
          -> (recurse : Data.Nat.lte numer predDenom = False)
          -> (numer `minus` (S predDenom)) `LTE` fuel
fuelLemma numer predDenom fuel enough recurse =
  let denom  : Nat
      denom = S predDenom
      numer' : Nat
      numer' = numer `minus` denom
      -- a bunch of inequational reasoning to show we have enough fuel
      -- on the recursive call
      denom_lte_numer : denom `LTE` numer
      denom_lte_numer = Properties.notlteIsLT numer predDenom recurse
      numer'_lt_numer : numer' `LT` numer
      numer'_lt_numer = (minusPosLT denom numer
                          (LTESucc LTEZero)
                          denom_lte_numer)
      succenough : S numer' `LTE` S fuel
      succenough = transitive {rel = LTE} numer'_lt_numer enough
  in fromLteSucc succenough

-- equivalence between the duplicate definitions in Data.Nar  ---

-- Internally, we use the two component definitions of divmod'
div'' : (fuel, numer, denom : Nat) -> Nat
div'' fuel numer denom = fst (divmod' fuel numer denom)

mod'' : (fuel, numer, denom : Nat) -> Nat
mod'' fuel numer denom = snd (divmod' fuel numer denom)


divmod'_eq_div'_mod' : (fuel, numer, denom : Nat)
            -> (divmod' fuel numer denom) = (div' fuel numer denom, mod' fuel numer denom)
divmod'_eq_div'_mod'   0       numer denom = Refl
divmod'_eq_div'_mod'  (S fuel) numer denom with (Data.Nat.lte numer denom)
 divmod'_eq_div'_mod' (S fuel) numer denom | True  = Refl
 divmod'_eq_div'_mod' (S fuel) numer denom | False =
   rewrite divmod'_eq_div'_mod' fuel (numer `minus` (S denom)) denom in
   Refl

div''_eq_div' : (fuel, numer, denom : Nat)
            -> div'' fuel numer denom = div' fuel numer denom
div''_eq_div' fuel numer denom = cong fst $
                                       divmod'_eq_div'_mod' fuel numer denom

mod''_eq_mod' : (fuel, numer, denom : Nat)
            -> mod'' fuel numer denom = mod' fuel numer denom
mod''_eq_mod' fuel numer denom = cong snd $
                                       divmod'_eq_div'_mod' fuel numer denom

export
divmodNatNZeqDivMod : (numer, denom : Nat) -> (0 prf1, prf2, prf3 : NonZero denom)
            -> (divmodNatNZ numer denom prf1) = (divNatNZ numer denom prf2, modNatNZ numer denom prf3)
divmodNatNZeqDivMod numer (S denom) prf1 prf2 prf3 = divmod'_eq_div'_mod' numer numer denom

export
fstDivmodNatNZeqDiv : (numer, denom : Nat) -> (0 prf1, prf2 : NonZero denom)
            -> (fst $ divmodNatNZ numer denom prf1) = divNatNZ numer denom prf2
fstDivmodNatNZeqDiv numer denom prf1 prf2 =
  rewrite divmodNatNZeqDivMod numer denom prf1 prf2 prf2 in
  Refl

export
sndDivmodNatNZeqMod : (numer, denom : Nat) -> (0 prf1, prf2 : NonZero denom)
            -> (snd $ divmodNatNZ numer denom prf1) = modNatNZ numer denom prf2
sndDivmodNatNZeqMod numer denom prf1 prf2 =
  rewrite divmodNatNZeqDivMod numer denom prf1 prf2 prf2 in
  Refl


-----------------------------------------------------------------------------
bound_mod'' : (fuel, numer, predDenom : Nat) -> (numer `LTE` fuel)
           -> (mod'' fuel numer predDenom) `LTE` predDenom
bound_mod'' 0        0     predDenom LTEZero = LTEZero
bound_mod'' (S fuel) numer predDenom enough  = case @@(Data.Nat.lte numer predDenom) of
  (True  ** numer_lte_predn)  => rewrite numer_lte_predn in
                                 Properties.lteIsLTE _ _ numer_lte_predn
  (False ** numer_gte_n    )  => rewrite numer_gte_n in
                                 bound_mod'' fuel (numer `minus` (S predDenom)) predDenom
                                                  (fuelLemma numer predDenom fuel enough numer_gte_n)

export
boundModNatNZ : (numer, denom : Nat) -> (0 denom_nz : NonZero denom)
              -> (modNatNZ numer denom denom_nz) `LT` denom
boundModNatNZ numer (S predDenom) denom_nz =
  LTESucc $
    rewrite sym $ mod''_eq_mod' numer numer predDenom in
      bound_mod'' numer numer predDenom $ reflexive {rel = LTE}
divisionTheorem' : (numer, predDenom : Nat)
                -> (fuel : Nat) -> (enough : numer `LTE` fuel)
                -> numer = (mod'' fuel numer predDenom) + (div'' fuel numer predDenom) * (S predDenom)

divisionTheorem'  0     predDenom  0       LTEZero = Refl
divisionTheorem'  numer predDenom (S fuel) enough with (@@(Data.Nat.lte numer predDenom))
 divisionTheorem' numer predDenom (S fuel) enough | (True ** prf)
   = rewrite prf in
     rewrite plusZeroRightNeutral numer in Refl
 divisionTheorem' numer predDenom (S fuel) enough | (False ** prf)
   = rewrite prf in
     let denom  : Nat
         denom = S predDenom
         numer' : Nat
         numer' = numer `minus` denom
         denom_lte_numer : denom `LTE` numer
         denom_lte_numer = Properties.notlteIsLT numer predDenom prf
         enough' : numer' `LTE` fuel
         enough' = fuelLemma numer predDenom fuel enough prf

         inductionHypothesis : (numer'
                             = (mod'' fuel numer' predDenom) +  (div'' fuel numer' predDenom) * denom)
         inductionHypothesis = divisionTheorem' numer' predDenom fuel enough'
     in sym $ Calc $
     |~ (mod'' fuel numer' predDenom) + (denom + (div'' fuel numer' predDenom) * denom)
     ~~ (mod'' fuel numer' predDenom) + ((div'' fuel numer' predDenom) * denom + denom)
               ...(cong ((mod'' fuel numer' predDenom) +) $ plusCommutative
                                                            denom
                                                            ((div'' fuel numer' predDenom) * denom))
     ~~((mod'' fuel numer' predDenom) +  (div'' fuel numer' predDenom) * denom) + denom
               ...(plusAssociative
                     (mod'' fuel numer' predDenom)
                     ((div'' fuel numer' predDenom) * denom)
                     denom)
     ~~ numer' + denom ...(cong (+ denom) $ sym inductionHypothesis)
     ~~ numer ...(plusMinusLte denom numer denom_lte_numer)



export
DivisionTheoremDivMod : (numer, denom : Nat)  -> (0 prf : NonZero denom)
               -> numer = snd ( divmodNatNZ numer denom prf)
                       + (fst $ divmodNatNZ numer denom prf)*denom
DivisionTheoremDivMod numer (S predDenom) prf
  = divisionTheorem' numer predDenom numer $ reflexive {rel = LTE}

export
DivisionTheorem : (numer, denom : Nat) -> (0 prf1, prf2 : NonZero denom)
               -> numer = (modNatNZ numer denom prf1) + (divNatNZ numer denom prf2)*denom
DivisionTheorem numer denom prf1 prf2
  = rewrite sym $ fstDivmodNatNZeqDiv numer denom prf1 prf2 in
    rewrite sym $ sndDivmodNatNZeqMod numer denom prf1 prf1 in
    DivisionTheoremDivMod numer denom prf1



divmodZeroZero : (denom, fuel : Nat)
           -> divmod' fuel 0 denom = (0,0)
divmodZeroZero denom  0       = Refl
divmodZeroZero denom (S fuel) = Refl

modZeroZero : (denom, fuel : Nat)
           -> mod'' fuel 0 denom = 0
modZeroZero denom fuel = rewrite divmodZeroZero denom fuel in Refl

divZeroZero : (denom, fuel : Nat)
           -> div'' fuel 0 denom = 0
divZeroZero denom fuel = rewrite divmodZeroZero denom fuel in Refl


divmodFuelLemma : (numer, denom, fuel1, fuel2 : Nat)
            -> (enough1 : fuel1 `GTE` numer)
            -> (enough2 : fuel2 `GTE` numer)
            -> divmod' fuel1 numer denom = divmod' fuel2 numer denom
divmodFuelLemma  0 denom 0 fuel2 LTEZero enough2 = rewrite divmodZeroZero denom fuel2 in
                                                Refl
divmodFuelLemma  0 denom (S fuel1) 0 enough1 LTEZero = Refl
divmodFuelLemma  numer denom (S fuel1) (S fuel2) enough1 enough2 with (@@(Data.Nat.lte numer denom))
 divmodFuelLemma numer denom (S fuel1) (S fuel2) enough1 enough2 | (True  ** prf)  =
   rewrite prf in Refl
 divmodFuelLemma numer denom (S fuel1) (S fuel2) enough1 enough2 | (False ** prf) =
   rewrite prf in
   rewrite divmodFuelLemma (numer `minus` (S denom)) denom fuel1 fuel2
             (fuelLemma numer denom fuel1 enough1 prf)
             (fuelLemma numer denom fuel2 enough2 prf) in
   Refl


multiplicationLemma : (q, predn, r : Nat) -> q * (S predn) + r `LTE` 0 -> (q = 0, r = 0)
multiplicationLemma q predn r bound =
  let r_eq_z : (r = 0)
      r_eq_z = zeroPlusRightZero (q * (S predn)) r (sym $ lteZeroIsZero bound)
      qn_eq_z : (q * (S predn) = 0)
      qn_eq_z = zeroPlusLeftZero (q * (S predn)) r (sym $ lteZeroIsZero bound)
      q_eq_z : q = 0
      q_eq_z = case zeroMultEitherZero q (S predn) qn_eq_z of
        Left  q_eq_0 => q_eq_0
        Right spred_eq_z impossible
  in (q_eq_z, r_eq_z)

multiplesModuloZero : (fuel, predn, k : Nat)
       -> (enough : fuel `GTE` k * (S predn) )
       -> mod' fuel (k * (S predn)) predn = 0
multiplesModuloZero 0        predn k enough =
  let (k_eq_z, _) = multiplicationLemma k predn 0 $
                    rewrite plusZeroRightNeutral (k * (S predn)) in
                    enough
  in rewrite k_eq_z in
  Refl
multiplesModuloZero  (S fuel) predn 0 enough = Refl
multiplesModuloZero  (S fuel) predn (S k) enough =
  let n : Nat
      n = S predn
      n_lte_skn : n `LTE` (1 + k)*n
      n_lte_skn = CalcWith {leq = LTE} $
        |~ n
        ~~ n  + 0     ...(sym $ plusZeroRightNeutral n)
        ~~ (1 + 0)*n ...(Refl)
        <~ (1 + k)*n   ...(multLteMonotoneLeft (1+0) (1+k) n $
                           plusLteMonotoneLeft 1 0 k LTEZero)
  in case @@(Data.Nat.lte ((1 + k)*n) predn) of
    (True  ** skn_lte_predn) => absurd $ irreflexive {rel = Data.Nat.LT}
                                       $ CalcWith {leq = LTE} $
      |~ 1 + predn
      ~~ n         ...(Refl)
      ~~ n + 0     ...(sym $ plusZeroRightNeutral n)
      ~~ (1 + 0)*n ...(Refl)
      <~ (1 + k)*n ...(multLteMonotoneLeft (1+0) (1+k) n $
                       LTESucc LTEZero)
      <~ predn     ...(Properties.lteIsLTE _ _ skn_lte_predn)
    (False ** prf) =>
      rewrite prf in
      let skn_minus_n_eq_kn : ((1 + k)*n `minus` n = k*n)
          skn_minus_n_eq_kn = Calc $
            |~ ((1+k)*n `minus` n)
            ~~ ((1+k)*n `minus` (n + 0)) ...(cong ((1+k)*n `minus`) $ sym $ plusZeroRightNeutral n)
            ~~ (n + k*n `minus` (n + 0)) ...(Refl)
            ~~ (k*n `minus` 0)           ...(plusMinusLeftCancel n (k*n) 0)
            ~~ k*n                       ...(minusZeroRight (k*n))
      in rewrite skn_minus_n_eq_kn in
      multiplesModuloZero fuel predn k $
      (rewrite sym $ skn_minus_n_eq_kn in
       fuelLemma ((1 + k)*n) predn fuel enough prf)

-- We also want to show uniqueness of this decomposition
-- This is, of course, quite horrible, but I want this theorem in the stdlib
addMultipleMod': (fuel1, fuel2, predn, a, b : Nat) -> (enough1 : fuel1 `GTE` b * (S predn) + a)
                                           -> (enough2 : fuel2 `GTE` a)
       -> mod'' fuel1 (b * (S predn) + a) predn = mod'' fuel2 a predn
addMultipleMod' 0         fuel2 predn a b enough1 enough2
  = let (b_eq_z, a_eq_z) = multiplicationLemma b predn a enough1
    in rewrite a_eq_z in
       rewrite b_eq_z in
       rewrite modZeroZero predn fuel2 in
       Refl
addMultipleMod' fuel1@(S _) fuel2 predn a 0 enough1 enough2 =
  rewrite divmodFuelLemma a predn fuel1 fuel2 enough1 enough2 in
  Refl
addMultipleMod' (S fuel1) fuel2 predn a (S k) enough1 enough2 =
  let n : Nat
      n = S predn
      lhsarg_geq_predn : ((1 + k)*n + a) `GT` predn
      lhsarg_geq_predn = CalcWith {leq = LTE} $
        |~ n
        ~~ (1+0)*n     ...(sym $ plusZeroRightNeutral n)
        <~ (1+k)*n     ...(multLteMonotoneLeft 1 (1+k) n $
                           LTESucc LTEZero)
        <~ (1+k)*n + a ...(lteAddRight $ (1+k)*n)
      prf1 : lte ((1 + k)*n + a) predn = False
      prf1 = GTIsnotlte ((1 + k)*n + a) predn lhsarg_geq_predn
      argsimplify : (((1 + k) *n + a ) `minus` n = k*n + a)
      argsimplify = Calc $
        |~ (((1+k)*n + a) `minus` n)
        ~~ (((n + k*n) + a) `minus` n)       ...(Refl)
        ~~ ((n + (k*n + a)) `minus` (n + 0)) ...(cong2 minus
                                                   (sym $ plusAssociative n (k*n) a)
                                                   (sym $ plusZeroRightNeutral n))
        ~~ ((k*n + a) `minus` 0)             ...(plusMinusLeftCancel n (k*n + a) 0)
        ~~ k*n + a                           ...(minusZeroRight (k*n + a))
  in rewrite prf1 in
     rewrite argsimplify in
     addMultipleMod' fuel1 fuel2 predn a k
       (rewrite sym argsimplify in
        fuelLemma ((1+k)*n + a) predn fuel1 enough1 prf1)
       enough2

addMultipleMod : (a, b, n : Nat) -> (0 n_neq_z1, n_neq_z2 : NonZero n)
              -> snd (divmodNatNZ (a*n + b) n n_neq_z1) = snd (divmodNatNZ b n n_neq_z2)
addMultipleMod a b n@(S predn) n_neq_z1  n_neq_z2 =
  addMultipleMod' (a*n + b) b predn b a (reflexive {rel = LTE}) (reflexive {rel = LTE})

modBelowDenom : (r, n : Nat) -> (0 n_neq_z : NonZero n)
             -> (r `LT` n)
             -> snd (divmodNatNZ r n n_neq_z)  = r
modBelowDenom 0 (S predn) n_neq_0 (LTESucc r_lte_predn) = Refl
modBelowDenom r@(S _) (S predn) n_neq_0 (LTESucc r_lte_predn) =
  rewrite LteIslte r predn r_lte_predn in
  Refl

modInjective : (r1, r2, n : Nat) -> (0 n_neq_z1, n_neq_z2 : NonZero n)
             -> (r1 `LT` n)
             -> (r2 `LT` n)
             -> snd (divmodNatNZ r1 n n_neq_z1)  = snd (divmodNatNZ r2 n n_neq_z2)
             -> r1 = r2
modInjective r1 r2 n n_neq_z1 n_neq_z2 r1_lt_n r2_lt_n ri_mod_eq = Calc $
  |~ r1
  ~~ snd (divmodNatNZ r1 n n_neq_z1) ...(sym $ modBelowDenom r1 n n_neq_z1 r1_lt_n)
  ~~ snd (divmodNatNZ r2 n n_neq_z2) ...(ri_mod_eq)
  ~~ r2                              ...(      modBelowDenom r2 n n_neq_z2 r2_lt_n)


step1 : (numer : Nat) -> (denom : Nat) -> (0 denom_nz : NonZero denom)
     -> (q, r : Nat) -> (r `LT` denom) -> (numer = q * denom + r)
     -> snd (divmodNatNZ numer denom denom_nz) = r
step1 x n n_nz q r r_lt_n x_eq_qnpr = Calc $
  |~ snd(divmodNatNZ x         n n_nz)
  ~~ snd(divmodNatNZ (q*n + r) n n_nz) ...(cong (\u => snd $ divmodNatNZ u n n_nz) $ x_eq_qnpr)
  ~~ snd(divmodNatNZ r         n n_nz) ...(addMultipleMod q r n n_nz n_nz)
  ~~ r                                 ...(modBelowDenom r n n_nz r_lt_n)

step2 : (numer : Nat) -> (denom : Nat) -> (0 denom_nz : NonZero denom)
     -> (q, r : Nat) -> (r `LT` denom) -> (numer = q * denom + r)
     -> fst (divmodNatNZ numer denom denom_nz) = q
step2 x n n_nz q r r_lt_n x_eq_qnr =
  let mod_eq_r : (snd (divmodNatNZ x n n_nz) = r)
      mod_eq_r = step1 x n n_nz q r r_lt_n x_eq_qnr

      two_decompositions : (fst $ divmodNatNZ x n n_nz) * n + r = q * n + r
      two_decompositions = Calc $
        |~ (fst $ divmodNatNZ x n n_nz) * n + r
        ~~ (fst $ divmodNatNZ x n n_nz) * n + (snd $ divmodNatNZ x n n_nz)
                                                       ...(cong (\ u =>
                                                                (fst $ divmodNatNZ x n n_nz)* n + u)
                                                                $ sym mod_eq_r)
        ~~ snd(divmodNatNZ x n n_nz) + fst (divmodNatNZ x n n_nz) * n
                                                       ...(plusCommutative _ _)
        ~~ x                                           ...(sym $ DivisionTheoremDivMod x n n_nz)
        ~~ q*n + r                                     ...(x_eq_qnr)

  in multRightCancel  (fst $ divmodNatNZ x n n_nz) q n n_nz
   $ plusRightCancel ((fst $ divmodNatNZ x n n_nz)* n) (q*n) r
   $ two_decompositions

export
DivisionTheoremUniquenessDivMod : (numer : Nat) -> (denom : Nat) -> (0 denom_nz : NonZero denom)
     -> (q, r : Nat) -> (r `LT` denom) -> (numer = q * denom + r)
     -> divmodNatNZ numer denom denom_nz = (q, r)
DivisionTheoremUniquenessDivMod numer denom denom_nz q r x prf =
  rewrite sym $ step1 numer denom denom_nz q r x prf in
  rewrite sym $ step2 numer denom denom_nz q r x prf in
  pair_eta _  -- Should idris be able to see this automatically? Maybe only with homogeneous equality?
  where
    -- Should this go elsewhere?
    ||| extensionality law for simple pairs
    pair_eta : (x : (a,b)) -> x = (fst x, snd x)
    pair_eta (x,y) = Refl

export
DivisionTheoremUniqueness : (numer : Nat) -> (denom : Nat) -> (0 denom_nz : NonZero denom)
     -> (q, r : Nat) -> (r `LT` denom) -> (numer = q * denom + r)
     -> (divNatNZ numer denom denom_nz = q, modNatNZ numer denom denom_nz = r)
DivisionTheoremUniqueness numer denom denom_nz q r x prf =
  rewrite sym $ fstDivmodNatNZeqDiv numer denom denom_nz denom_nz in
  rewrite sym $ sndDivmodNatNZeqMod numer denom denom_nz denom_nz in
  rewrite DivisionTheoremUniquenessDivMod numer denom denom_nz q r x prf in
  (Refl, Refl)
