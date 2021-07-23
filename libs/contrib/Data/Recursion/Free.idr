||| Module partially based on McBride's paper:
||| Turing-Completeness Totally Free
|||
||| It gives us a type to describe computation using general recursion
||| and functions to run these computations for a while or to completion
||| if we are able to prove them total.
|||
||| The content of the Erased section is new. Instead of producing the
||| domain/evaluation pair by computing a Dybjer-Setzer code we build a
||| specialised structure that allows us to make the domain proof runtime
||| irrelevant.

module Data.Recursion.Free

import Data.Late
import Data.InductionRecursion.DybjerSetzer

%default total

------------------------------------------------------------------------
-- Type

||| Syntax for a program using general recursion
public export
data General : (a : Type) -> (b : a -> Type) -> (x : Type) -> Type where
  ||| We can return a value without performing any recursive call.
  Tell : x -> General a b x
  ||| Or we can pick an input and ask an oracle to give us a return value
  ||| for it. The second argument is a continuation explaining what we want
  ||| to do with the returned value.
  Ask  : (i : a) -> (b i -> General a b x) -> General a b x

||| Type of functions using general recursion
public export
PiG : (a : Type) -> (b : a -> Type) -> Type
PiG a b = (i : a) -> General a b (b i)

||| Recursor for General
public export
fold : (x -> y) -> ((i : a) -> (b i -> y) -> y) -> General a b x -> y
fold pure ask (Tell x) = pure x
fold pure ask (Ask i k) = ask i (\ o => fold pure ask (k o))

------------------------------------------------------------------------
-- Basic functions

||| Perform a recursive call and return the value provided by the oracle.
public export
call : PiG a b
call i = Ask i Tell

||| Monadic bind (defined outside of the interface to be able to use it for
||| map and (<*>)).
public export
bind : General a b x -> (x -> General a b y) -> General a b y
bind m f = fold f Ask m

||| Given a monadic oracle we can give a monad morphism interpreting a
||| function using general recursion as a monadic process.
public export
monadMorphism : Monad m => (t : (i : a) -> m (b i)) -> General a b x -> m x
monadMorphism t = fold pure (\ i => (t i >>=))

------------------------------------------------------------------------
-- Instances

public export
Functor (General a b) where
  map f = fold (Tell . f) Ask

public export
Apply (General a b) where
  gf <*> gv = bind gf (\ f => map (f $) gv)

public export
Applicative (General a b) where
  pure = Tell

public export
Bind (General a b) where
  (>>=) = bind

public export
Monad (General a b) where

------------------------------------------------------------------------
-- Fuel-based (partial) evaluation

||| Check whehther we are ready to return a value
public export
already : General a b x -> Maybe x
already = monadMorphism (\ i => Nothing)

||| Use a function using general recursion to expand all of the oracle calls.
public export
expand : PiG a b -> General a b x -> General a b x
expand f = monadMorphism f

||| Recursively call expand a set number of times.
public export
engine : PiG a b -> Nat -> General a b x -> General a b x
engine f Z     = id
engine f (S n) = engine f n . expand f

||| Check whether recursively calling expand a set number of times is enough
||| to produce a value.
public export
petrol : PiG a b -> Nat -> (i : a) -> Maybe (b i)
petrol f n i = already $ engine f n $ f i

------------------------------------------------------------------------
-- Late-based evaluation

||| Rely on an oracle using general recursion to convert a function using
||| general recursion into a process returning a value in the (distant) future.
public export
late : PiG a b -> General a b x -> Late x
late f = monadMorphism (\ i => Later (assert_total $ late f (f i)))

||| Interpret a function using general recursion as a process returning
||| a value in the (distant) future.
public export
lazy : PiG a b -> (i : a) -> Late (b i)
lazy f i = late f (f i)

------------------------------------------------------------------------
-- Domain as a Dybjer-Setzer code and total evaluation function

namespace DybjerSetzer

  ||| Compute, as a Dybjer-Setzer code for an inductive-recursive type, the domain
  ||| of a function defined by general recursion.
  public export
  Domain : PiG a b -> (i : a) -> Code b (b i)
  Domain f i = monadMorphism ask (f i) where

    ask : (i : a) -> Code b (b i)
    ask i = Branch () (const i) $ \ t => Yield (t ())

  ||| If a given input is in the domain of the function then we may evaluate
  ||| it fully on that input and obtain a pure return value.
  public export
  evaluate : (f : PiG a b) -> (i : a) -> Mu (Domain f) i -> b i
  evaluate f i inDom = Decode inDom

  ||| If every input value is in the domain then the function is total.
  public export
  totally : (f : PiG a b) -> ((i : a) -> Mu (Domain f) i) ->
            (i : a) -> b i
  totally f allInDomain i = evaluate f i (allInDomain i)

------------------------------------------------------------------------
-- Runtime irrelevant domain and total evaluation function

namespace Erased

  ------------------------------------------------------------------------
  -- Domain and evaluation functions

  ||| What it means to describe a terminating computation
  ||| @ f is the function used to answer questions put to the oracle
  ||| @ d is the description of the computation
  public export
  data Layer : (f : PiG a b) -> (d : General a b (b i)) -> Type

  ||| The domain of a function (i.e. the set of inputs for which it terminates)
  ||| as a predicate on inputs
  ||| @ f is the function whose domain is being described
  ||| @ i is the input that is purported to be in the domain
  Domain : (f : PiG a b) -> (i : a) -> Type

  ||| Fully evaluate a computation known to be terminating.
  ||| Because of the careful design of the inductive family Layer, we can make
  ||| the proof runtime irrelevant.
  evaluateLayer : (f : PiG a b) -> (d : General a b (b i)) -> (0 _ : Layer f d) -> b i

  ||| Fully evaluate a function call for an input known to be in its domain.
  evaluate : (f : PiG a b) -> (i : a) -> (0 _ : Domain f i) -> b i

  -- In a classic Dybjer-Setzer situation this is computed by induction over the
  -- index of type `General a b (b i)` and the fixpoint called `Domain` is the
  -- one thing defined as an inductive type.
  -- Here we have to flip the script because Idris will only trust inductive data
  -- as a legitimate source of termination metric for a recursive function. This
  -- makes our definition of `evaluateLayer` obviously terminating.
  data Layer : PiG a b -> General a b (b i) -> Type where
    ||| A computation returning a value is trivially terminating
    MkTell : {0 a : Type} -> {0 b : a -> Type} -> {0 f : PiG a b} -> {0 i : a} ->
             (o : b i) -> Layer f (Tell o)

    ||| Performing a call to the oracle is termnating if the input is in its
    ||| domain and if the rest of the computation is also finite.
    MkAsk  : {0 a : Type} -> {0 b : a -> Type} -> {0 f : PiG a b} -> {0 i : a} ->
             (j : a) -> (jprf : Domain f j) ->
             (k : b j -> General a b (b i)) -> Layer f (k (evaluate f j jprf)) ->
             Layer f (Ask j k)

  -- Domain is simply defined as the top layer leading to a terminating
  -- computation with the function used as its own oracle.
  Domain f i = Layer f (f i)

  ||| A view that gives us a pattern-matching friendly presentation of the
  ||| @ d computation known to be terminating
  ||| @ l proof that it is
  ||| This may seem like a useless definition but the function `view`
  ||| demonstrates a very important use case: even if the proof is runtime
  ||| irrelevant, we can manufacture a satisfying view of it.
  data View : {d : General a b (b i)} -> (l : Layer f d) -> Type where
    TView : {0 b : a -> Type} -> {0 f : PiG a b} -> (o : b i) -> View (MkTell {b} {f} o)
    AView : {0 f : PiG a b} ->
            (j : a) -> (0 jprf : Domain f j) ->
            (k : b j -> General a b (b i)) -> (0 kprf : Layer f (k (evaluate f j jprf))) ->
            View (MkAsk j jprf k kprf)

  ||| Function computing the view by pattern-matching on the computation and
  ||| inverting the proof. Note that the proof is runtime irrelevant even though
  ||| the resulting view is not: this is possible because the relevant constructor
  ||| is uniquely determined by the shape of `d`.
  public export
  view : (d : General a b (b i)) -> (0 l : Layer f d) -> View l
  view (Tell o)  (MkTell o)            = TView o
  view (Ask j k) (MkAsk j jprf k kprf) = AView j jprf k kprf

  -- Just like `Domain` is defined in terms of `Layer`, the evaluation of a
  -- function call for an input in its domain can be reduced to the evaluation
  -- of a layer.
  evaluate f i l = evaluateLayer f (f i) l

  -- The view defined earlier allows us to pattern on the runtime irrelevant
  -- proof that the layer describes a terminating computation and therefore
  -- define `evaluateLayer` in a way that is purely structural.
  -- This becomes obvious if one spells out the (forced) pattern corresponding
  -- to `d` in each branch of the case.
  evaluateLayer f d l = case view d l of
    TView o => o
    AView j jprf k kprf => evaluateLayer f (k (evaluate f j jprf)) kprf

  ||| If a function's domain is total then it is a pure function.
  public export
  totally : (f : PiG a b) -> (0 _ : (i : a) -> Domain f i) ->
            (i : a) -> b i
  totally f dom i = evaluate f i (dom i)

  ------------------------------------------------------------------------
  -- Proofs

  ||| Domain is a singleton type
  export
  irrelevantDomain : (f : PiG a b) -> (i : a) -> (p, q : Domain f i) -> p === q

  ||| Layer is a singleton type
  irrelevantLayer
    : (f : PiG a b) -> (d : General a b (b i)) -> (l, m : Layer f d) -> l === m

  irrelevantDomain f i p q = irrelevantLayer f (f i) p q

  irrelevantLayer f (Tell o)
    (MkTell o) (MkTell o) = Refl
  irrelevantLayer f (Ask j k)
    (MkAsk j jprf1 k kprf1) (MkAsk j jprf2 k kprf2)
    with (irrelevantDomain f j jprf1 jprf2)
      irrelevantLayer f (Ask j k)
        (MkAsk j jprf k kprf1) (MkAsk j jprf k kprf2)
        | Refl = cong (MkAsk j jprf k)
               $ irrelevantLayer f (k (evaluate f j jprf)) kprf1 kprf2

  ||| The result of `evaluateLayer` does not depend on the specific proof that
  ||| `i` is in the domain of the layer of computation at hand.
  export
  evaluateLayerIrrelevance
    : (f : PiG a b) -> (d : General a b (b i)) -> (0 p, q : Layer f d) ->
      evaluateLayer f d p === evaluateLayer f d q
  evaluateLayerIrrelevance f d p q
    = rewrite irrelevantLayer f d p q in Refl

  ||| The result of `evaluate` does not depend on the specific proof that `i`
  ||| is in the domain of the function at hand.
  export
  evaluateIrrelevance
    : (f : PiG a b) -> (i : a) -> (0 p, q : Domain f i) ->
      evaluate f i p === evaluate f i q
  evaluateIrrelevance f i p q
    = evaluateLayerIrrelevance f (f i) p q

  ||| The result computed by a total function is independent from the proof
  ||| that it is total.
  export
  totallyIrrelevance
    : (f : PiG a b) -> (0 p, q : (i : a) -> Domain f i) ->
      (i : a) -> totally f p i === totally f q i
  totallyIrrelevance f p q i = evaluateIrrelevance f i (p i) (q i)
