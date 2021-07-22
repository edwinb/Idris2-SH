||| A segment is a compositional fragment of a telescope.
||| A key difference is that segments are right-nested, whereas
||| telescopes are left nested.
||| So telescopes are convenient for well-bracketing dependencies,
||| but segments are convenient for processing telescopes from left
||| to right.
|||
||| As with telescopes, indexing segments by their length (hopefully)
||| helps the type-checker infer stuff.
module Data.Telescope.Segment

import Data.Telescope.Telescope

import Syntax.PreorderReasoning
import Data.Fin
import Data.Nat
import Data.DPair

%default total

||| A segment is a compositional fragment of a telescope, indexed by
||| the segment's length.
public export
data Segment : (n : Nat) -> Left.Telescope k -> Type where
  Nil  : Segment 0 gamma
  (::) : (ty : TypeIn gamma) -> (delta : Segment n (gamma -. ty)) -> Segment (S n) gamma

||| A segment of size `n` indexed by `gamma` can be seen as the tabulation of a
||| function that turns environments for `gamma` into telescopes of size `n`.
public export
tabulate : (n : Nat) -> (Left.Environment gamma -> Left.Telescope n) -> Segment n gamma
tabulate Z tel = []
tabulate (S n) tel = (sigma :: tabulate n (uncurry delta)) where

  sigma : TypeIn gamma
  sigma env = fst (uncons (tel env))

  delta : (env : Environment gamma) -> sigma env -> Left.Telescope n
  delta env v with (uncons (tel env))
    delta env v | (sig ** delt ** _) = delt v

||| Any telescope is a segment in the empty telescope. It amounts to looking
||| at it left-to-right instead of right-to-left.
public export
fromTelescope : {k : Nat} -> Left.Telescope k -> Segment k []
fromTelescope gamma = tabulate _ (const gamma)

||| Conversely, a segment of size `n` in telescope `gamma` can be seen as a function
||| from environments for `gamma` to telescopes of size `n`.
public export
untabulate : {n : Nat} -> Segment n gamma -> (Left.Environment gamma -> Left.Telescope n)
untabulate []            _   = []
untabulate (ty :: delta) env = cons (ty env) (untabulate delta . (\ v => (env ** v)))

||| Any segment in the empty telescope correspond to a telescope.
public export
toTelescope : {k : Nat} -> Segment k [] -> Left.Telescope k
toTelescope seg = untabulate seg ()

%name Segment delta,delta',delta1,delta2

infixl 3 |++, :++

||| This lemma comes up all the time when mixing induction on Nat with
||| indexing modulo addition.  An alternative is to use something like
||| frex.
succLemma : (lft, rgt : Nat) -> lft + (S rgt) = S (lft + rgt)
succLemma x y = Calc $
  |~ x + (1 + y)
  ~~ (x + 1)+ y  ...(plusAssociative x 1 y)
  ~~ (1 + x)+ y  ...(cong (+y) $ plusCommutative x 1)
  ~~ 1 + (x + y) ...(sym $ plusAssociative 1 x y)

-- Should go somehwere in stdlib
public export
keep : (0 prf : a ~=~ b) -> a ~=~ b
keep Refl = Refl

-- Keeping the `Nat` argument relevant, should (hopefully) only
-- case-split on it and not the environment unnecessarily, allowing us
-- to calculate, so long as we know the 'shape' of the Segment.
--
-- This should work in theory, I don't think it actually works for
-- Idris at the moment.  Might work in Agda?

||| Segments act on telescope from the right.
public export
(|++) : (gamma : Left.Telescope k) -> {n : Nat} -> (delta : Segment n gamma) -> Left.Telescope (n + k)
(|++)  gamma {n = 0} delta  = gamma
(|++)  gamma {n=S n} (ty :: delta) = rewrite sym $ succLemma n k in
                                       gamma -. ty |++ delta

||| Segments form a kind of an indexed monoid w.r.t. the action `(|++)`
public export
(++) : {gamma : Left.Telescope k}
    -> {n : Nat}
    -> (lft : Segment n  gamma         )
    -> (rgt : Segment m (gamma |++ lft))
    -> Segment (n + m) gamma
(++) {n = 0  } delta       rgt = rgt
(++) {n = S n} (ty :: lft) rgt = ty :: lft ++ rewrite succLemma n k in
                                              rgt
-- This monoid does act on telescopes:
export
actSegmentAssociative : (gamma : Left.Telescope k)
                     -> (lft : Segment n gamma)
                     -> (rgt : Segment m (gamma |++ lft))
                     -> (gamma |++ (lft ++ rgt)) ~=~ ((gamma |++ lft) |++ rgt)
actSegmentAssociative gamma {n = 0}   []          rgt = Refl
actSegmentAssociative gamma {n = S n} (ty :: lft) rgt =
  let rgt' : Segment {k = n + (S k)} m (gamma -. ty |++ lft)
      rgt' = rewrite succLemma n k in
             rgt
      rgt_eq_rgt' : rgt ~=~ rgt'
      rgt_eq_rgt' = rewrite succLemma n k in
                    Refl
  in
  rewrite sym $ succLemma (n + m) k in
  rewrite sym $ succLemma n       k in keep $ Calc $
  |~ ((gamma -. ty) |++ (lft ++ rgt'))
  ~~ ((gamma -. ty |++  lft) |++ rgt')
          ...(actSegmentAssociative (gamma -. ty) lft rgt')

public export
weaken : {0 gamma : Left.Telescope k}
      -> {delta : Segment n gamma} -> (sy : TypeIn gamma)
      -> TypeIn (gamma |++ delta)
weaken           {delta = []         } sy = sy
weaken {n = S n} {delta = ty :: delta} sy = rewrite sym $ succLemma n k in
                                            weaken (weakenTypeIn sy)

public export
projection : {0 gamma : Left.Telescope k}
          -> {n : Nat}
          -> {0 delta : Segment n gamma}
          -> Environment (gamma |++ delta)
          -> Environment gamma
projection {n = 0  } {delta = []         } env = env
projection {n = S n} {delta = ty :: delta} env
  = let (env' ** _) = projection {n} {delta}
                    $ rewrite succLemma n k in env
    in env'

infixl 4 .=

public export
data Environment : (env : Left.Environment gamma)
                -> (delta : Segment n gamma) -> Type where
  Empty : Environment env []
  (.=) : {0 gamma : Left.Telescope k} -> {0 ty : TypeIn gamma}
      -> {0 env   : Left.Environment gamma}
      -> {0 delta : Segment n (gamma -. ty)}

      -> (x : ty env) -> (xs : Segment.Environment (env ** x) delta)
      -> Environment env (ty :: delta)

public export
(:++) : {0 gamma : Left.Telescope k} -> {0 delta : Segment n gamma}
     -> (env : Left.Environment gamma)
     -> (ext : Segment.Environment env delta)
     ->        Left.Environment (gamma |++ delta)
(:++) env Empty = env
(:++) {n = S n} env (x .= xs) = rewrite sym $ succLemma n k in
                                (env ** x) :++ xs

-- This is too nasty for now, leave to later
{-
public export
break : {0 k : Nat} -> (gamma : Telescope k') -> (pos : Position gamma)
     -> {auto 0 ford : k' = cast pos + k } -> Telescope k
break gamma          FZ      {ford = Refl} = gamma
break []            (FS pos) {ford = _   } impossible
break {k' = S k'} (gamma -. ty) (FS pos) {ford} = break gamma pos
  {ford = Calc $
   |~ k'
   ~~ cast pos + k ...(succInjective _ _ ford)}

-- Should go into Data.Fin
export
lastIsLast : {n : Nat} -> cast (last {n}) = n
lastIsLast {n = 0  } = Refl
lastIsLast {n = S n} = rewrite lastIsLast {n} in
                       Refl

public export
finComplement : {n : Nat} -> (i : Fin n) -> Fin n
finComplement FZ = last
finComplement (FS i) = weaken (finComplement i)

export
castNaturality : (i : Fin n) -> finToNat (weaken i) ~=~ finToNat i
castNaturality  FZ    = Refl
castNaturality (FS i) = rewrite castNaturality i in
                        Refl

export
finComplementSpec : (i : Fin (S n)) -> cast i + cast (finComplement i) = n
finComplementSpec FZ = keep lastIsLast
finComplementSpec {n = .(S n)} (FS i@ FZ   ) = rewrite castNaturality (finComplement i) in
                                               rewrite finComplementSpec i in
                                               Refl
finComplementSpec {n = .(S n)} (FS i@(FS _)) = rewrite castNaturality (finComplement i) in
                                               rewrite finComplementSpec i in
                                               Refl

complementLastZero : (n : Nat) -> finComplement (last {n}) = FZ
complementLastZero n = finToNatInjective _ _ $ plusLeftCancel n _ _ $ Calc $
   let n' : Nat
       n' = cast $ finComplement $ last {n} in
   |~ n + n'
   ~~ (finToNat $ last {n})  + n'
                    ...(cong (+n') $ sym $ lastIsLast {n})
   ~~ n             ...(finComplementSpec $ last {n})
   ~~ n         + 0 ...(sym $ plusZeroRightNeutral n)

public export
breakOnto : {0 k,k' : Nat} -> (gamma : Telescope k) -> (pos : Position gamma)
         -> (delta : Segment n gamma)
         -> {auto 0 ford1 : k' === (finToNat $ finComplement pos) }
         -> {default
               -- disgusting, sorry
               (replace {p = \u => k = finToNat pos + u}
                        (sym ford1)
                        (sym $ finComplementSpec pos))
             0 ford2 : (k === ((finToNat pos) + k')) }
         -> Segment (cast pos + n)
                    (break {k = k'}
                           gamma pos
                           {ford = ford2})
breakOnto gamma          FZ      delta {ford1 = Refl} {ford2} =
                         rewrite sym ford2 in
                         delta
breakOnto (gamma -. ty) (FS pos) delta {ford1 = Refl} {ford2} =
                         rewrite sym $ succLemma (cast pos) n in
                         rewrite castNaturality (finComplement pos) in
                         breakOnto gamma pos (ty :: delta)

uip : (prf1, prf2 : x ~=~ y) -> prf1 ~=~ prf2
uip Refl Refl = Refl

export
breakStartEmpty : (gamma : Telescope k')
               -> {auto 0 ford1 : k = 0}
               -> {auto 0 ford2 : k' = finToNat (start gamma) + k}
               -> break {k} {k'} gamma (start gamma) {ford = ford2}
                ~=~ Telescope.Nil
breakStartEmpty [] {ford1 = Refl} {ford2 = Refl}            = Refl
breakStartEmpty {k} {k' = S k'} {ford1} {ford2} (gamma -. ty) =
                -- Yuck!
                let 0 u : (k' = finToNat (start gamma) + k)
                    u = succInjective _ _ ford2
                    v : break {k} {k'} gamma (start gamma) {ford = u}
                        ~=~ Telescope.Nil
                    v = breakStartEmpty {k} {k'} gamma {ford2 = u}
                in replace {p = \z =>
                             Equal {a = Telescope k} {b = Telescope 0}
                                   (break {k'} {k} gamma (start gamma)
                                          {ford = z})
                                          []
                        }
                        (uip u _)
                        (keep v)



public export
projection : {0 gamma : Telescope k} -> (pos : Position gamma) -> (env : Environment gamma)
          -> Environment (break {k = cast (finComplement pos)} gamma pos
                                {ford = sym $ finComplementSpec pos})
projection FZ env = rewrite finComplementSpec $ FZ {k} in
                    env
projection {gamma = []} (FS pos) Empty impossible
projection {k = S k} {gamma = gamma -. ty} (FS pos) (env ** x) =
  rewrite castNaturality (finComplement pos) in
  projection {k} pos env
-}
