------------------------------------------------------------------------
-- This module is based on the following papers:

-- Categories of Containers
-- Abbott, Altenkirch, Ghani

-- Derivatives of Containers
-- Abbott, Altenkirch, Ghani, McBride
------------------------------------------------------------------------

module Data.Container

import Data.Either
import Decidable.Equality

%default total

------------------------------------------------------------------------
-- Container and their morphisms
-- * Extension is a functor from Container to Type

-- Objects of the category of containers
namespace Container

  public export
  record Container where
    constructor MkContainer
    Shape : Type
    Position : Shape -> Type

  public export
  record Extension (c : Container) (x : Type) where
    constructor MkExtension
    shape    : Shape c
    payloads : Position c shape -> x

  ||| The image of a container by @Extension@ is a functor
  public export
  Functor (Extension c) where map f (MkExtension s p) = MkExtension s (f . p)

-- Morphisms of the category of containers
namespace Morphism

  public export
  record Morphism (c, d : Container) where
    constructor MkMorphism
    shapeMorphism : Shape c -> Shape d
    positionMorphism : {s : Shape c} -> Position d (shapeMorphism s) -> Position c s

  public export
  Extension : Morphism c d -> Extension c x -> Extension d x
  Extension phi (MkExtension s p)
    = MkExtension (shapeMorphism phi s) (p . positionMorphism phi)

------------------------------------------------------------------------
-- Combinators to build containers

namespace Combinators

  -- Constant
  public export
  Const : Type -> Container
  Const k = MkContainer k (const Void)

  export
  toConst : k -> Extension (Const k) x
  toConst v = MkExtension v absurd

  export
  fromConst : Extension (Const k) x -> k
  fromConst (MkExtension v _) = v

  -- Identity
  public export
  Identity : Container
  Identity = MkContainer () (\ () => ())

  export
  toIdentity : x -> Extension Identity x
  toIdentity v = MkExtension () (const v)

  export
  fromIdentity : Extension Identity x -> x
  fromIdentity (MkExtension () chld) = chld ()

  -- Composition
  public export
  Compose : (d, c : Container) -> Container
  Compose d c = MkContainer
    (Extension d (Shape c))
    (\ (MkExtension shp chld) => (p : Position d shp ** Position c (chld p)))

  export
  toCompose : (Extension d . Extension c) x -> Extension (Compose d c) x
  toCompose (MkExtension shp1 chld)
    = MkExtension (MkExtension shp1 (shape . chld)) (\ (p ** q) => payloads (chld p) q)

  export
  fromCompose : Extension (Compose d c) x -> (Extension d . Extension c) x
  fromCompose (MkExtension (MkExtension shp1 shp2) chld)
    = MkExtension shp1 (\ p => MkExtension (shp2 p) (\ q => chld (p ** q)))

  -- Direct sum
  public export
  Sum : (c, d : Container) -> Container
  Sum c d = MkContainer (Either (Shape c) (Shape d)) (either (Position c) (Position d))

  export
  toSum : Either (Extension c x) (Extension d x) -> Extension (Sum c d) x
  toSum (Left (MkExtension shp chld)) = MkExtension (Left shp) chld
  toSum (Right (MkExtension shp chld)) = MkExtension (Right shp) chld

  export
  fromSum : Extension (Sum c d) x -> Either (Extension c x) (Extension d x)
  fromSum (MkExtension (Left shp) chld) = Left (MkExtension shp chld)
  fromSum (MkExtension (Right shp) chld) = Right (MkExtension shp chld)

  -- Pairing
  public export
  Pair : (c, d : Container) -> Container
  Pair c d = MkContainer (Shape c, Shape d) (\ (p, q) => Either (Position c p) (Position d q))

  export
  toPair : (Extension c x, Extension d x) -> Extension (Pair c d) x
  toPair (MkExtension shp1 chld1, MkExtension shp2 chld2)
    = MkExtension (shp1, shp2) (either chld1 chld2)

  export
  fromPair : Extension (Pair c d) x -> (Extension c x, Extension d x)
  fromPair (MkExtension (shp1, shp2) chld)
    = (MkExtension shp1 (chld . Left), MkExtension shp2 (chld . Right))

  -- Branching over a Type
  public export
  Exponential : Type -> Container -> Container
  Exponential k c = MkContainer (k -> Shape c) (\ p => (v : k ** Position c (p v)))

  export
  toExponential : (k -> Extension c x) -> Extension (Exponential k c) x
  toExponential f = MkExtension (shape . f) (\ (v ** p) => payloads (f v) p)

  export
  fromExponential : Extension (Exponential k c) x -> (k -> Extension c x)
  fromExponential (MkExtension  shp chld) k = MkExtension (shp k) (\ p => chld (k ** p))

------------------------------------------------------------------------
-- Taking various fixpoints of containers

namespace Initial

  public export
  data W : Container -> Type where
    MkW : Extension c (W c) -> W c

  export
  map : Morphism c d -> W c -> W d
  map f (MkW (MkExtension shp chld)) = MkW $ Extension f (MkExtension shp (\ p => map f (chld p)))
  --  Container.map inlined because of -------------------^
  --  termination checking

  export
  foldr : (Extension c x -> x) -> W c -> x
  foldr alg (MkW (MkExtension shp chld)) = alg (MkExtension shp (\ p => foldr alg (chld p)))

  export
  para : (Extension c (x, W c) -> x) -> W c -> x
  para alg (MkW (MkExtension shp chld)) = alg (MkExtension shp (\ p => let w = chld p in (para alg w, w)))

namespace Monad

  ||| @Free@ is a wrapper around @W@ to make it inference friendly.
  ||| Without this wrapper, neither @pure@ nor @bind@ are able to infer their @c@ argument.
  public export
  record Free (c : Container) (x : Type) where
    constructor MkFree
    runFree : W (Sum c (Const x))

  export
  pure : x -> Free c x
  pure x = MkFree $ MkW (toSum (Right (toConst x)))

  export
  (>>=) : Free c x -> (x -> Free c y) -> Free c y
  (>>=) (MkFree mx) k = foldr (alg . fromSum {c} {d = Const x}) mx where

    alg : Either (Extension c (Free c y)) (Extension (Const x) (Free c y)) -> Free c y
    alg  = either (MkFree . MkW . toSum {c} {d = Const y} . Left . map (runFree {c}))
                  (k . fromConst {k = x})

  export
  join : Free c (Free c x) -> Free c x
  join = (>>= id)

namespace Final

  public export
  data M : Container -> Type where
    MkM : Extension c (Inf (M c)) -> M c

  export
  unfoldr : (s -> Extension c s) -> s -> M c
  unfoldr next seed =
    let (MkExtension shp chld) = next seed in
    MkM (MkExtension shp (\ p => unfoldr next (chld p)))

namespace Comonad

  ||| @Cofree@ is a wrapper around @M@ to make it inference friendly.
  ||| Without this wrapper, neither @extract@ nor @extend@ are able to infer their @c@ argument.
  public export
  record Cofree (c : Container) (x : Type) where
    constructor MkCofree
    runCofree : M (Pair (Const x) c)

  export
  extract : Cofree c x -> x
  extract (MkCofree (MkM m)) = fst (shape m)

  export
  extend : (Cofree c a -> b) -> Cofree c a -> Cofree c b
  extend alg = MkCofree . unfoldr next . runCofree where

    next : M (Pair (Const a) c) -> Extension (Pair (Const b) c) (M (Pair (Const a) c))
    next m@(MkM layer) =
      let (_, (MkExtension shp chld)) = fromPair {c = Const a} layer in
      let b = toConst (alg (MkCofree m)) in
      toPair (b, MkExtension shp (\ p => chld p))
-- Eta-expanded to force Inf ------^

  export
  duplicate : Cofree c a -> Cofree c (Cofree c a)
  duplicate = extend id

------------------------------------------------------------------------
-- Derivative

namespace Derivative

  public export
  Derivative : Container -> Container
  Derivative c = MkContainer
    (s : Shape c ** Position c s)
    (\ (s ** p) => (p' : Position c s ** Not (p === p')))

  export
  hole : (v : Extension (Derivative c) x) -> Position c (fst (shape v))
  hole (MkExtension (shp ** p) _) = p

  export
  unplug : (v : Extension c x) -> Position c (shape v) -> (Extension (Derivative c) x, x)
  unplug (MkExtension shp chld) p = (MkExtension (shp ** p) (chld . fst), chld p)

  export
  plug : (v : Extension (Derivative c) x) -> DecEq (Position c (fst (shape v))) => x -> Extension c x
  plug (MkExtension (shp ** p) chld) x = MkExtension shp $ \ p' => case decEq p p' of
    Yes eq => x
    No neq => chld (p' ** neq)

  export
  toConst : Extension (Const Void) x -> Extension (Derivative (Const k)) x
  toConst v = absurd (fromConst v)

  export
  fromConst : Extension (Derivative (Const k)) x -> Extension (Const Void) x
  fromConst v = absurd (hole {c = Const _} v)

  export
  toIdentity : Extension (Derivative Identity) x
  toIdentity = MkExtension (() ** ()) (\ (() ** eq) => absurd (eq Refl))

  export
  toSum : Extension (Sum (Derivative c) (Derivative d)) x ->
          Extension (Derivative (Sum c d)) x
  toSum v = case fromSum {c = Derivative c} {d = Derivative d} v of
    Left (MkExtension (shp ** p) chld) => MkExtension (Left shp ** p) chld
    Right (MkExtension (shp ** p) chld) => MkExtension (Right shp ** p) chld

  export
  fromSum : Extension (Derivative (Sum c d)) x ->
            Extension (Sum (Derivative c) (Derivative d)) x
  fromSum (MkExtension (shp ** p) chld) = toSum {c = Derivative c} {d = Derivative d} $ case shp of
    Left shp => Left (MkExtension (shp ** p) chld)
    Right shp => Right (MkExtension (shp ** p) chld)

  export
  toPair : Extension (Sum (Pair (Derivative c) d) (Pair c (Derivative d))) x ->
           Extension (Derivative (Pair c d)) x
  toPair v = case fromSum {c = Pair (Derivative c) d} {d = Pair c (Derivative d)} v of
    Left p => let (MkExtension (shp1 ** p1) chld1, MkExtension shp2 chld2) = fromPair {c = Derivative c} p in
              MkExtension ((shp1, shp2) ** Left p1) $ \ (p' ** neq) => case p' of
                  Left p1' => chld1 (p1' ** (neq . cong Left))
                  Right p2' => chld2 p2'
    Right p => let (MkExtension shp1 chld1, MkExtension (shp2 ** p2) chld2) = fromPair {c} {d = Derivative d} p in
               MkExtension ((shp1, shp2) ** Right p2) $ \ (p' ** neq) => case p' of
                  Left p1' => chld1 p1'
                  Right p2' => chld2 (p2' ** (neq . cong Right))

  export
  fromPair : Extension (Derivative (Pair c d)) x ->
             Extension (Sum (Pair (Derivative c) d) (Pair c (Derivative d))) x
  fromPair (MkExtension ((shp1, shp2) ** p) chld) = case p of
    Left p1 => toSum {c = Pair (Derivative c) d} {d = Pair c (Derivative d)}
                     (Left (MkExtension ((shp1 ** p1), shp2) $ either
                         (\ p1' => chld (Left (DPair.fst p1') ** DPair.snd p1' . injective))
                         (\ p2 => chld (Right p2 ** absurd))))
    Right p2 => toSum {c = Pair (Derivative c) d} {d = Pair c (Derivative d)}
                     (Right (MkExtension (shp1, (shp2 ** p2)) $ either
                         (\ p1 => chld (Left p1 ** absurd))
                         (\ p2' => chld (Right (DPair.fst p2') ** DPair.snd p2' . injective))))


  export
  fromCompose : Extension (Derivative (Compose c d)) x ->
                Extension (Pair (Derivative d) (Compose (Derivative c) d)) x
  fromCompose (MkExtension (MkExtension shp1 shp2 ** (p1 ** p2)) chld)
    = toPair (left, right) where

      left : Extension (Derivative d) x
      left = MkExtension (shp2 p1 ** p2)
           $ \ (p2' ** neqp2) => chld ((p1 ** p2') ** neqp2 . mkDPairInjectiveSnd)

      right : Extension (Compose (Derivative c) d) x
      right = toCompose
            $ MkExtension (shp1 ** p1)
            $ \ (p1' ** neqp1) => MkExtension (shp2 p1')
                                 $ \ p2' => chld ((p1' ** p2') ** (neqp1 . cong fst))

  export
  toCompose : ((s : _) -> DecEq (Position c s)) -> ((s : _) -> DecEq (Position d s)) ->
              Extension (Pair (Derivative d) (Compose (Derivative c) d)) x ->
              Extension (Derivative (Compose c d)) x
  toCompose dec1 dec2 v with (fromPair {c = Derivative d} {d = Compose (Derivative c) d} v)
    toCompose dec1 dec2 v | (MkExtension (shp2 ** p2) chld2, w) with (fromCompose w)
      toCompose dec1 dec2 v
        | (MkExtension (shp2 ** p2) chld2, w)
        | (MkExtension (shp1 ** p1) chld1)
        = MkExtension (MkExtension shp1 (\ p1' => shp2' p1' (decEq @{dec1 shp1} p1 p1')) **
                      (p1 ** (p2' (decEq @{dec1 shp1} p1 p1))))
        $ \ ((p1' ** p2'') ** neq) => chld2' p1' p2'' neq

         where
          shp2' : (p1' : Position c shp1) -> Dec (p1 === p1') -> Shape d
          shp2' p1' (Yes eq) = shp2
          shp2' p1' (No neq) = shape (chld1 (p1' ** neq))

          p2' : (eq : Dec (p1 === p1)) -> Position d (shp2' p1 eq)
          p2' (Yes Refl) = p2
          p2' (No neq)   = absurd (neq Refl)

          chld2' : (p1' : Position c shp1) ->
                   (p2'' : Position d (shp2' p1' (decEq @{dec1 shp1} p1 p1'))) ->
                   (neq : Not (MkDPair p1 (p2' (decEq @{dec1 shp1} p1 p1)) = MkDPair p1' p2'')) -> x
          chld2' p1' p2'' neq with (decEq @{dec1 shp1} p1 p1')
            chld2' p1' p2'' neq | No neq1 = payloads (chld1 (p1' ** neq1)) p2''
            chld2' _ p2'' neq | Yes Refl with (decEq @{dec1 shp1} p1 p1)
              chld2' _ p2'' neq | Yes Refl | No argh = absurd (argh Refl)
              chld2' _ p2'' neq | Yes Refl | Yes Refl with (decEq @{dec2 shp2} p2 p2'')
                chld2' _ p2'' neq | Yes Refl | Yes Refl | No neq2 = chld2 (p2'' ** neq2)
                chld2' _ _ neq | Yes Refl | Yes Refl | Yes Refl = absurd (neq Refl)
