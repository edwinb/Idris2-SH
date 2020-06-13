module Data.Nat.Factor

import Control.Relation
import Control.WellFounded
import Data.Fin
import Data.Fin.Extra
import Data.Nat
import Data.Nat.Equational
import Syntax.PreorderReasoning

%default total


||| Factor n p is a witness that p is indeed a factor of n,
||| i.e. there exists a q such that p * q = n.
public export
data Factor : Nat -> Nat -> Type where
    CofactorExists : {p, n : Nat} -> (q : Nat) -> n = p * q -> Factor p n

||| NotFactor n p is a witness that p is NOT a factor of n,
||| i.e. there exist a q and an r, greater than 0 but smaller than p,
||| such that p * q + r = n.
public export
data NotFactor : Nat -> Nat -> Type where
    ZeroNotFactorS : (n : Nat) -> NotFactor Z (S n)
    ProperRemExists : {p, n : Nat} -> (q : Nat) ->
        (r : Fin (pred p)) ->
        n = p * q + S (finToNat r) ->
        NotFactor p n

||| DecFactor n p is a result of the process which decides
||| whether or not p is a factor on n.
public export
data DecFactor : Nat -> Nat -> Type where
    ItIsFactor : Factor p n -> DecFactor p n
    ItIsNotFactor : NotFactor p n -> DecFactor p n

||| CommonFactor n m p is a witness that p is a factor of both n and m.
public export
data CommonFactor : Nat -> Nat -> Nat -> Type where
    CommonFactorExists : {a, b : Nat} -> (p : Nat) -> Factor p a -> Factor p b -> CommonFactor p a b

||| GCD n m p is a witness that p is THE greatest common factor of both n and m.
||| The second argument to the constructor is a function which for all q being
||| a factor of both n and m, proves that q is a factor of p.
|||
||| This is equivalent to a more straightforward definition, stating that for
||| all q being a factor of both n and m, q is less than or equal to p, but more
||| powerful and therefore more useful for further proofs. See below for a proof
||| that if q is a factor of p then q must be less than or equal to p.
public export
data GCD : Nat -> Nat -> Nat -> Type where
    MkGCD : {a, b, p : Nat} ->
        {auto notBothZero : NotBothZero a b} ->
        (CommonFactor p a b) ->
        ((q : Nat) -> CommonFactor q a b -> Factor q p) ->
        GCD p a b


Uninhabited (Factor Z (S n)) where
    uninhabited (CofactorExists q prf) = uninhabited prf

||| Given a statement that p is factor of n, return its cofactor.
export
cofactor : Factor p n -> (q : Nat ** Factor q n)
cofactor (CofactorExists {n} {p} q prf) =
        (q ** CofactorExists p $ rewrite multCommutative q p in prf)

||| 1 is a factor of any natural number.
export
oneIsFactor : (n : Nat) -> Factor 1 n
oneIsFactor Z = CofactorExists Z Refl
oneIsFactor (S k) = CofactorExists (S k) (rewrite plusZeroRightNeutral k in Refl)

||| 1 is the only factor of itself
export
oneSoleFactorOfOne : (a : Nat) -> Factor a 1 -> a = 1
oneSoleFactorOfOne Z (CofactorExists q prf) = absurd $ uninhabited prf
oneSoleFactorOfOne (S Z) (CofactorExists _ _) = Refl
oneSoleFactorOfOne (S (S k)) (CofactorExists Z prf) =
        absurd . uninhabited $ replace {p = \x => 1 = x} (multZeroRightZero k) prf
oneSoleFactorOfOne (S (S k)) (CofactorExists (S j) prf) =
        absurd . uninhabited . succInjective 0 (S j + (j + (k * S j))) $
        replace {p = \x => 1 = S x} (sym $ plusSuccRightSucc j (j + (k * S j))) prf

||| Every natural number is factor of itself.
export
Reflexive Nat Factor where
  reflexive {x} = CofactorExists 1 $ rewrite multOneRightNeutral x in Refl

||| Factor relation is transitive. If b is factor of a and c is b factor of c
||| is also a factor of a.
export
Transitive Nat Factor where
  transitive {x} (CofactorExists qb prfAB) (CofactorExists qc prfBC) =
    CofactorExists (qb * qc) $
        rewrite prfBC in
        rewrite prfAB in
        rewrite multAssociative x qb qc in
        Refl

multOneSoleNeutral : (a, b : Nat) -> S a = S a * b -> b = 1
multOneSoleNeutral Z b prf =
        rewrite sym $ plusZeroRightNeutral b in
        sym prf
multOneSoleNeutral (S k) Z prf =
        absurd . uninhabited $
        replace {p = \x => S (S k) = x} (multZeroRightZero k) prf
multOneSoleNeutral (S k) (S Z) prf = Refl
multOneSoleNeutral (S k) (S (S j)) prf =
        absurd . uninhabited .
        subtractEqLeft k {b = 0} {c = S j + S (j + (k * S j))} $
        rewrite plusSuccRightSucc j (S (j + (k * S j))) in
        rewrite plusZeroRightNeutral k in
        rewrite plusAssociative k j (S (S (j + (k * S j)))) in
        rewrite sym $ plusCommutative j k in
        rewrite sym $ plusAssociative j k (S (S (j + (k * S j)))) in
        rewrite sym $ plusSuccRightSucc k (S (j + (k * S j))) in
        rewrite sym $ plusSuccRightSucc k (j + (k * S j)) in
        rewrite plusAssociative k j (k * S j) in
        rewrite plusCommutative k j in
        rewrite sym $ plusAssociative j k (k * S j) in
        rewrite sym $ multRightSuccPlus k (S j) in
        succInjective k (j + (S (S (j + (k * (S (S j))))))) $
        succInjective (S k) (S (j + (S (S (j + (k * (S (S j)))))))) prf

||| If a is a factor of b and b is a factor of a, then we can conclude a = b.
export
factorAntisymmetric : {a, b : Nat} -> Factor a b -> Factor b a -> a = b
factorAntisymmetric {a = 0} (CofactorExists qa prfAB) (CofactorExists qb prfBA) = sym prfAB
factorAntisymmetric {a = S a} {b = 0} (CofactorExists qa prfAB) (CofactorExists qb prfBA) = prfBA
factorAntisymmetric {a = S a} {b = S b} (CofactorExists qa prfAB) (CofactorExists qb prfBA) =
    let qIs1 = multOneSoleNeutral a (qa * qb) $
            rewrite multAssociative (S a) qa qb in
            rewrite sym prfAB in
            prfBA
    in
    rewrite prfAB in
    rewrite oneSoleFactorOfOne qa . CofactorExists qb $ sym qIs1 in
    rewrite multOneRightNeutral a in
    Refl

||| No number can simultaneously be and not be a factor of another number.
export
factorNotFactorAbsurd : {n, p : Nat} -> Factor p n -> NotFactor p n -> Void
factorNotFactorAbsurd {n = S k} {p = Z} (CofactorExists q prf) (ZeroNotFactorS k) =
        uninhabited prf
factorNotFactorAbsurd {n} {p} (CofactorExists q prf) (ProperRemExists q' r contra) with (cmp q q')
    factorNotFactorAbsurd {n} {p} (CofactorExists q prf) (ProperRemExists (q + S d) r contra) | CmpLT d =
        SIsNotZ .
        subtractEqLeft (p * q) {b = S ((p * S d) + finToNat r)} {c = 0} $
        rewrite plusZeroRightNeutral (p * q) in
        rewrite plusSuccRightSucc (p * S d) (finToNat r) in
        rewrite plusAssociative (p * q) (p * S d) (S (finToNat r)) in
        rewrite sym $ multDistributesOverPlusRight p q (S d) in
        rewrite sym contra in
        rewrite sym prf in
        Refl
    factorNotFactorAbsurd {n} {p} (CofactorExists q prf) (ProperRemExists q r contra) | CmpEQ =
        uninhabited .
        subtractEqLeft (p * q) {b = (S (finToNat r))} {c = 0} $
        rewrite plusZeroRightNeutral (p * q) in
        rewrite sym contra in
        prf
    factorNotFactorAbsurd {n} {p} (CofactorExists (q + S d) prf) (ProperRemExists q r contra) | CmpGT d =
        let srEQpPlusPD = the (plus p (mult p d) = S (finToNat r)) $
                rewrite sym $ multRightSuccPlus p d in
                subtractEqLeft (p * q) {b = p * (S d)} {c = S (finToNat r)} $
                    rewrite sym $ multDistributesOverPlusRight p q (S d) in
                    rewrite sym contra in
                    sym prf
        in
        case p of
            Z => uninhabited srEQpPlusPD
            (S k) =>
                succNotLTEzero .
                subtractLteLeft k {b = S (d + (k * d))} {c = 0} $
                rewrite sym $ plusSuccRightSucc k (d + (k * d)) in
                rewrite plusZeroRightNeutral k in
                rewrite srEQpPlusPD in
                elemSmallerThanBound r


||| Anything is a factor of 0.
export
anythingFactorZero : (a : Nat) -> Factor a 0
anythingFactorZero a = CofactorExists 0 (sym $ multZeroRightZero a)

||| For all natural numbers p and q, p is a factor of (p * q).
export
multFactor : (p, q : Nat) -> Factor p (p * q)
multFactor p q = CofactorExists q Refl

||| If n > 0 then any factor of n must be less than or equal to n.
export
factorLteNumber : Factor p n -> {auto positN : LTE 1 n} -> LTE p n
factorLteNumber (CofactorExists Z prf) =
        let nIsZero = replace {p = \x => n = x} (multZeroRightZero p) prf
            oneLteZero = replace {p = LTE 1} nIsZero positN
        in
        absurd $ succNotLTEzero oneLteZero
factorLteNumber (CofactorExists (S k) prf) =
        rewrite prf in
        leftFactorLteProduct p k

||| If p is a factor of n, then it is also a factor of (n + p).
export
plusDivisorAlsoFactor : Factor p n -> Factor p (n + p)
plusDivisorAlsoFactor (CofactorExists q prf) =
        CofactorExists (S q)
            rewrite plusCommutative n p in
            rewrite multRightSuccPlus p q in
            cong (plus p) prf

||| If p is NOT a factor of n, then it also is NOT a factor of (n + p).
export
plusDivisorNeitherFactor : NotFactor p n -> NotFactor p (n + p)
plusDivisorNeitherFactor (ZeroNotFactorS k) =
        rewrite plusZeroRightNeutral k in
        ZeroNotFactorS k
plusDivisorNeitherFactor (ProperRemExists q r remPrf) =
        ProperRemExists (S q) r
            rewrite multRightSuccPlus p q in
            rewrite sym $ plusAssociative p (p * q) (S $ finToNat r) in
            rewrite plusCommutative p ((p * q) + S (finToNat r)) in
            rewrite remPrf in
            Refl

||| If p is a factor of n, then it is also a factor of any multiply of n.
export
multNAlsoFactor : Factor p n -> (a : Nat) -> {auto aok : LTE 1 a} -> Factor p (n * a)
multNAlsoFactor _ Z = absurd $ succNotLTEzero aok
multNAlsoFactor (CofactorExists q prf) (S a) =
        CofactorExists (q * S a)
            rewrite prf in
            sym $ multAssociative p q (S a)

||| If p is a factor of both n and m, then it is also a factor of their sum.
export
plusFactor : Factor p n -> Factor p m -> Factor p (n + m)
plusFactor (CofactorExists qn prfN) (CofactorExists qm prfM) =
        rewrite prfN in
        rewrite prfM in
        rewrite sym $ multDistributesOverPlusRight p qn qm in
        multFactor p (qn + qm)

||| If p is a factor of a sum (n + m) and a factor of n, then it is also
||| a factor of m. This could be expressed more naturally with minus, but
||| it would be more difficult to prove, since minus lacks certain properties
||| that one would expect from decent subtraction.
export
minusFactor : {a, b, p : Nat} -> Factor p (a + b) -> Factor p a -> Factor p b
minusFactor (CofactorExists qab prfAB) (CofactorExists qa prfA) =
        CofactorExists (minus qab qa) (
            rewrite multDistributesOverMinusRight p qab qa in
            rewrite sym prfA in
            rewrite sym prfAB in
            replace {p = \x => b = minus (a + b) x} (plusZeroRightNeutral a)
            rewrite plusMinusLeftCancel a b 0 in
            rewrite minusZeroRight b in
            Refl
        )

||| A decision procedure for whether of not p is a factor of n.
export
decFactor : (n, d : Nat) -> DecFactor d n
decFactor Z Z = ItIsFactor $ reflexive {x = Z}
decFactor (S k) Z = ItIsNotFactor $ ZeroNotFactorS k
decFactor n (S d) =
        let Fraction n (S d) q r prf = Data.Fin.Extra.divMod n (S d) in
        case r of
            FZ =>
                let prf =
                        replace {p = \x => x = n} (plusZeroRightNeutral (q + (d * q))) $
                        replace {p = \x => x + 0 = n} (multCommutative q (S d)) prf
                in
                ItIsFactor $ CofactorExists q (sym prf)

            (FS pr) =>
                ItIsNotFactor $ ProperRemExists q pr (
                        rewrite multCommutative d q in
                        rewrite sym $ multRightSuccPlus q d in
                        sym prf
                    )

||| For all p greater than 1, if p is a factor of n, then it is NOT a factor
||| of (n + 1).
export
factNotSuccFact : {n, p : Nat} -> GT p 1 -> Factor p n -> NotFactor p (S n)
factNotSuccFact {p = Z} pGt1 (CofactorExists q prf) =
        absurd $ succNotLTEzero pGt1
factNotSuccFact {p = S Z} pGt1 (CofactorExists q prf) =
        absurd . succNotLTEzero $ fromLteSucc pGt1
factNotSuccFact {p = S (S k)} pGt1 (CofactorExists q prf) =
        ProperRemExists q FZ (
            rewrite sym prf in
            rewrite plusCommutative n 1 in
            Refl
        )

||| The relation of common factor is symmetric, that is if p is a common factor
||| of n and m, then it is also a common factor if m and n.
export
commonFactorSym : CommonFactor p a b -> CommonFactor p b a
commonFactorSym (CommonFactorExists p pfa pfb) = CommonFactorExists p pfb pfa

||| The relation of greates common divisor is symmetric.
export
gcdSym : GCD p a b -> GCD p b a
gcdSym {a = Z} {b = Z} (MkGCD {notBothZero} _ _) impossible
gcdSym {a = S a} {b} (MkGCD {notBothZero = LeftIsNotZero} cf greatest) =
        MkGCD {notBothZero = RightIsNotZero} (commonFactorSym cf) $
        \q, cf => greatest q (commonFactorSym cf)
gcdSym {a} {b = S b} (MkGCD {notBothZero = RightIsNotZero} cf greatest) =
        MkGCD {notBothZero = LeftIsNotZero} (commonFactorSym cf) $
        \q, cf => greatest q (commonFactorSym cf)

||| If p is a common factor of a and b, then it is also a factor of their GCD.
||| This actually follows directly from the definition of GCD.
export
commonFactorAlsoFactorOfGCD : {p : Nat} -> Factor p a -> Factor p b -> GCD q a b -> Factor p q
commonFactorAlsoFactorOfGCD pfa pfb (MkGCD _ greatest) =
        greatest p (CommonFactorExists p pfa pfb)


||| 1 is a common factor of any pair of natural numbers.
export
oneCommonFactor : (a, b : Nat) -> CommonFactor 1 a b
oneCommonFactor a b = CommonFactorExists 1
        (CofactorExists a (rewrite plusZeroRightNeutral a in Refl))
        (CofactorExists b (rewrite plusZeroRightNeutral b in Refl))

||| Any natural number is a common factor of itself and itself.
export
selfIsCommonFactor : (a : Nat) -> {auto ok : LTE 1 a} -> CommonFactor a a a
selfIsCommonFactor Z = absurd $ succNotLTEzero ok
selfIsCommonFactor (S k) =
  let prf = reflexive {x = S k} in
    CommonFactorExists (S k) prf prf

-- Some helpers for the gcd function.
data Search : Type where
    SearchArgs : (a, b : Nat) -> LTE b a -> {auto bNonZero : LTE 1 b} -> Search

left : Search -> Nat
left (SearchArgs l _ _) = l

right : Search -> Nat
right (SearchArgs _ r _) = r

Sized Search where
    size (SearchArgs a b _) = a + b

notLteAndGt : (a, b : Nat) -> LTE a b -> GT a b -> Void
notLteAndGt Z b aLteB aGtB = succNotLTEzero aGtB
notLteAndGt (S k) Z aLteB aGtB = succNotLTEzero aLteB
notLteAndGt (S k) (S j) aLteB aGtB = notLteAndGt k j (fromLteSucc aLteB) (fromLteSucc aGtB)

gcd_step : (x : Search) ->
    (rec : (y : Search) -> Smaller y x ->  (f : Nat ** GCD f (left y) (right y))) ->
    (f : Nat ** GCD f (left x) (right x))
gcd_step (SearchArgs Z _ bLteA {bNonZero}) _ = absurd . succNotLTEzero $ transitive {ty = Nat} bNonZero bLteA
gcd_step (SearchArgs _ Z _ {bNonZero}) _ = absurd $ succNotLTEzero bNonZero
gcd_step (SearchArgs (S a) (S b) bLteA {bNonZero}) rec = case divMod (S a) (S b) of
    Fraction (S a) (S b) q FZ prf =>
        let sbIsFactor = the (S a = plus q (mult b q))
                rewrite multCommutative b q in
                rewrite sym $ multRightSuccPlus q b in
                replace {p = \x => S a = x} (plusZeroRightNeutral (q * S b)) $ sym prf
            skDividesA = CofactorExists q sbIsFactor
            skDividesB = reflexive {x = S b}
            greatest = the
                ((q' : Nat) -> CommonFactor q' (S a) (S b) -> Factor q' (S b))
                (\q', (CommonFactorExists q' _ qfb) => qfb)
        in
        (S b ** MkGCD (CommonFactorExists (S b) skDividesA skDividesB) greatest)

    Fraction (S a) (S b) q (FS r) prf =>
            let rLtSb = lteSuccRight $ elemSmallerThanBound r
                qGt1 = the (LTE 1 q) $ case q of
                    Z => absurd . notLteAndGt (S $ finToNat r) b (elemSmallerThanBound r) $
                        replace {p = LTE (S b)} (sym prf) bLteA
                    (S k) => LTESucc LTEZero
                smaller = the (LTE (S (S (plus b (S (finToNat r))))) (S (plus a (S b)))) $
                    rewrite plusCommutative a (S b) in
                    LTESucc . LTESucc . plusLteLeft b . fromLteSucc $ transitive {ty = Nat} (elemSmallerThanBound $ FS r) bLteA
                (f ** MkGCD (CommonFactorExists f prfSb prfRem) greatestSbSr) =
                    rec (SearchArgs (S b) (S $ finToNat r) rLtSb) smaller
                prfSa = the (Factor f (S a)) $
                    rewrite sym prf in
                    rewrite multCommutative q (S b) in
                    plusFactor (multNAlsoFactor prfSb q) prfRem
                greatest = the
                    ((q' : Nat) -> CommonFactor q' (S a) (S b) -> Factor q' f)
                    (\q', (CommonFactorExists q' qfa qfb) =>
                        let sbfqSb =
                                the (Factor (S b) (q * S b)) $
                                rewrite multCommutative q (S b) in
                                multFactor (S b) q
                            rightPrf = minusFactor {a = q * S b} {b = S (finToNat r)}
                                (rewrite prf in qfa)
                                (transitive {ty = Nat} qfb sbfqSb)
                        in
                        greatestSbSr q' (CommonFactorExists q' qfb rightPrf)
                    )
            in
            (f ** MkGCD (CommonFactorExists f prfSa prfSb) greatest)

||| An implementation of Euclidean Algorithm for computing greatest common
||| divisors. It is proven correct and total; returns a proof that computed
||| number actually IS the GCD. Unfortunately it's very slow, so improvements
||| in terms of efficiency would be welcome.
export
gcd : (a, b : Nat) -> {auto ok : NotBothZero a b} -> (f : Nat ** GCD f a b)
gcd Z Z impossible
gcd Z b =
    (b ** MkGCD (CommonFactorExists b (anythingFactorZero b) (reflexive {x = b})) $
        \q, (CommonFactorExists q _ prf) => prf
    )
gcd a Z =
    (a ** MkGCD (CommonFactorExists a (reflexive {x = a}) (anythingFactorZero a)) $
        \q, (CommonFactorExists q prf _) => prf
    )
gcd (S a) (S b) with (cmp (S a) (S b))
    gcd (S (b + S d)) (S b) | CmpGT d =
        let aGtB = the (LTE (S b) (S (b + S d))) $
                rewrite sym $ plusSuccRightSucc b d in
                LTESucc . lteSuccRight $ lteAddRight b
        in
        sizeInd gcd_step $ SearchArgs (S (b + S d)) (S b) aGtB
    gcd (S a) (S a)         | CmpEQ =
        let greatest = the
                ((q : Nat) -> CommonFactor q (S a) (S a) -> Factor q (S a))
                (\q, (CommonFactorExists q qfa _) => qfa)
        in
        (S a ** MkGCD (selfIsCommonFactor (S a)) greatest)
    gcd (S a) (S (a + S d)) | CmpLT d =
        let aGtB = the (LTE (S a) (S (plus a (S d)))) $
                rewrite sym $ plusSuccRightSucc a d in
                LTESucc . lteSuccRight $ lteAddRight a
            (f ** MkGCD prf greatest) = sizeInd gcd_step $ SearchArgs (S (a + S d)) (S a) aGtB
        in
        (f ** MkGCD (commonFactorSym prf) (\q, cf => greatest q $ commonFactorSym cf))

||| For every two natural numbers there is a unique greatest common divisor.
export
gcdUnique : {a, b, p, q : Nat} -> GCD p a b -> GCD q a b -> p = q
gcdUnique (MkGCD pCFab greatestP) (MkGCD qCFab greatestQ) =
    factorAntisymmetric (greatestQ p pCFab) (greatestP q qCFab)


divByGcdHelper : (a, b, c : Nat) -> GCD (S a) (S a * S b) (S a * c) -> GCD 1 (S b) c
divByGcdHelper a b c (MkGCD _ greatest) =
    MkGCD (CommonFactorExists 1 (oneIsFactor (S b)) (oneIsFactor c)) $
    \q, (CommonFactorExists q (CofactorExists qb prfQB) (CofactorExists qc prfQC)) =>
        let qFab = CofactorExists {n = S a * S b} {p = q * S a} qb
                rewrite multCommutative q (S a) in
                rewrite sym $ multAssociative (S a) q qb in
                rewrite sym $ prfQB in
                Refl
            qFac = CofactorExists {n = S a * c} {p = q * S a} qc
                rewrite multCommutative q (S a) in
                rewrite sym $ multAssociative (S a) q qc in
                rewrite sym $ prfQC in
                Refl
            CofactorExists f prfQAfA =
                greatest (q * S a) (CommonFactorExists (q * S a) qFab qFac)
            qf1 = multOneSoleNeutral a (f * q)
                rewrite multCommutative f q in
                rewrite multAssociative (S a) q f in
                rewrite sym $ multCommutative q (S a) in
                prfQAfA
        in
        CofactorExists f
            rewrite multCommutative q f in
            sym qf1


||| For every two natural numbers, if we divide both of them by their GCD,
||| the GCD of resulting numbers will always be 1.
export
divByGcdGcdOne : {a, b, c : Nat} -> GCD a (a * b) (a * c) -> GCD 1 b c
divByGcdGcdOne {a = Z} (MkGCD {notBothZero = LeftIsNotZero} _ _) impossible
divByGcdGcdOne {a = Z} (MkGCD {notBothZero = RightIsNotZero} _ _) impossible
divByGcdGcdOne {a = S a} {b = Z} {c = Z} (MkGCD {notBothZero} _ _) =
        case replace {p = \x => NotBothZero x x} (multZeroRightZero (S a)) notBothZero of
            LeftIsNotZero impossible
            RightIsNotZero impossible
divByGcdGcdOne {a = S a} {b = Z} {c = S c} gcdPrf@(MkGCD {notBothZero} _ _) =
        case replace {p = \x => NotBothZero x (S a * S c)} (multZeroRightZero (S a)) notBothZero of
            LeftIsNotZero impossible
            RightIsNotZero => gcdSym $ divByGcdHelper a c Z $ gcdSym gcdPrf
divByGcdGcdOne {a = S a} {b = S b} {c = Z} gcdPrf@(MkGCD {notBothZero} _ _) =
        case replace {p = \x => NotBothZero (S a * S b) x} (multZeroRightZero (S a)) notBothZero of
            RightIsNotZero impossible
            LeftIsNotZero => divByGcdHelper a b Z gcdPrf
divByGcdGcdOne {a = S a} {b = S b} {c = S c} gcdPrf =
        divByGcdHelper a b (S c) gcdPrf
