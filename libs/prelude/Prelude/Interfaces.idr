module Prelude.Interfaces

import Builtin
import Prelude.Basics
import Prelude.EqOrd
import Prelude.Num
import Prelude.Ops

%default total

-------------
-- ALGEBRA --
-------------

||| Sets equipped with a single binary operation that is associative.  Must
||| satisfy the following laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
public export
interface Semigroup ty where
  constructor MkSemigroup
  (<+>) : ty -> ty -> ty

||| Sets equipped with a single binary operation that is associative, along with
||| a neutral element for that binary operation.  Must satisfy the following
||| laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Neutral for `<+>`:
|||     forall a, a <+> neutral == a
|||     forall a, neutral <+> a == a
public export
interface Semigroup ty => Monoid ty where
  constructor MkMonoid
  neutral : ty

public export
Semigroup () where
  _ <+> _ = ()

public export
Monoid () where
  neutral = ()

public export
Semigroup Ordering where
  LT <+> _ = LT
  GT <+> _ = GT
  EQ <+> o =  o

public export
Monoid Ordering where
  neutral = EQ

public export
Semigroup b => Semigroup (a -> b) where
  (f <+> g) x = f x <+> g x

public export
Monoid b => Monoid (a -> b) where
  neutral _ = neutral

---------------------------------------------------------
-- FUNCTOR, APPLY, APPLICATIVE, MONAD
---------------------------------------------------------

||| Functors allow a uniform action over a parameterised type.
||| @ f a parameterised type
public export
interface Functor f where
  constructor MkFunctor
  ||| Apply a function across everything of type 'a' in a parameterised type
  ||| @ f the parameterised type
  ||| @ func the function to apply
  map : (func : a -> b) -> f a -> f b

||| An infix alias for `map`, applying a function across everything of type 'a'
||| in a parameterised type.
||| @ f the parameterised type
||| @ func the function to apply
public export
(<$>) : Functor f => (func : a -> b) -> f a -> f b
(<$>) func x = map func x

||| Flipped version of `<$>`, an infix alias for `map`, applying a function across
||| everything of type 'a' in a parameterised type.
||| @ f the parameterised type
||| @ func the function to apply
public export
(<&>) : Functor f => f a -> (func : a -> b) -> f b
(<&>) x func = map func x

||| Run something for effects, replacing the return value with a given parameter.
public export
(<$) : Functor f => b -> f a -> f b
(<$) b = map (const b)

||| Flipped version of `<$`.
public export
($>) : Functor f => f a -> b -> f b
($>) fa b = map (const b) fa

||| Run something for effects, throwing away the return value.
%inline
public export
ignore : Functor f => f a -> f ()
ignore = map (const ())

namespace Functor
  ||| Composition of functors is a functor.
  public export
  [Compose] (Functor f, Functor g) => Functor (f . g) where
    map = map . map

||| An applicative functor without `pure`.
|||
||| This allows us to get access to `(<*>)` and
||| possibly `(>>=)` for data types, for which we cannot
||| define `pure`, such as sorted maps or vectors
||| (fixed length lists). In case of vectors, it is possible
||| to implement `pure`, but only if we have access to the
||| vector's length (see the implementations of
||| `Apply` and `Applicative` for `Data.Vect` in base).
|||
||| In the case of `Pair`, we can get `(<*>)` and
||| `(>>=)` for pairs whose first value is a `Semigroup`, while
||| for `pure` we'd need a `Monoid`.
public export
interface Functor f => Apply f where
  constructor MkApply
  (<*>) : f (a -> b) -> f a -> f b

public export
(<*) : Apply f => f a -> f b -> f a
a <* b = map const a <*> b

public export
(*>) : Apply f => f a -> f b -> f b
a *> b = map (const id) a <*> b

%allow_overloads (<*)
%allow_overloads (*>)

namespace Apply
  ||| Composition of applicative functors is an applicative functor.
  public export
  [Compose] (Apply f, Apply g) => Apply (f . g)
    using Functor.Compose where
      fun <*> x = (<*>) <$> fun <*> x

public export
[SemigroupApply] Apply f => Semigroup a => Semigroup (f a) where
  x <+> y = (<+>) <$> x <*> y

public export
interface Apply f => Applicative f where
  constructor MkApplicative
  pure : a -> f a

%allow_overloads pure

||| Conditionally execute an applicative expression when the boolean is true.
public export
when : Applicative f => Bool -> Lazy (f ()) -> f ()
when True f = f
when False f = pure ()

||| Execute an applicative expression unless the boolean is true.
%inline public export
unless : Applicative f => Bool -> Lazy (f ()) -> f ()
unless = when . not

namespace Applicative
  ||| Composition of applicative functors is an applicative functor.
  public export
  [Compose] (Applicative f, Applicative g) => Applicative (f . g)
    using Apply.Compose where
      pure = pure . pure

public export
[MonoidApplicative] Applicative f => Monoid a => Monoid (f a) using Interfaces.SemigroupApply where
  neutral = pure neutral

public export
interface Apply m => Bind m where
  constructor MkBind
  ||| Also called `bind`.
  (>>=) : m a -> (a -> m b) -> m b

  ||| Also called `flatten` or mu.
  join : m (m a) -> m a

  -- default implementations
  (>>=) x f = join (f <$> x)
  join x = x >>= id

public export
interface Applicative m => Bind m => Monad m where
  constructor MkMonad

%allow_overloads (>>=)

||| Right-to-left monadic bind, flipped version of `>>=`.
public export
(=<<) : Bind m => (a -> m b) -> m a -> m b
(=<<) = flip (>>=)

||| Sequencing of effectful composition
public export
(>>) : Bind m => m () -> Lazy (m b) -> m b
a >> b = a >>= \_ => b

||| Left-to-right Kleisli composition of monads.
public export
(>=>) : Bind m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>=>) f g = \x => f x >>= g

||| Right-to-left Kleisli composition of monads, flipped version of `>=>`.
public export
(<=<) : Bind m => (b -> m c) -> (a -> m b) -> (a -> m c)
(<=<) = flip (>=>)

---------------------------------------------------------
-- ALT, PLUS, ALTERNATIVE
---------------------------------------------------------

||| The Alt interface identifies an associative
||| operation on a type constructor. It is similar to Semigroup,
||| except that it applies to types of kind `Type -> Type`,
||| like `Maybe` or `List`.
|||
||| `Alt` implementations are required to satisfy the following laws:
|||
|||     Associativity: `(x <|> y) <|> z = x <|> (y <|> z)`
|||     Distributivity: `f <$> (x <|> y) = (f <$> x) <|> (f <$> y)`
|||
||| A common use case is to select the first "valid" item, or,
||| if all items are "invalid", the last "invalid" item
||| (see the `Alt` implementation for `Either e` for this
||| behavior).
public export
interface Functor f => Alt f where
  constructor MkAlt
  (<|>) : f a -> Lazy (f a) -> f a

||| The Plus interface class extends Alt with a value that should
||| be the left and right identity for `(<|>)`.
|||
||| It is similar to `Monoid`, except that it applies to types
||| of kind `Type -> Type`, like `Maybe` or `List`.
|||
||| `Plus` implementations should satisfy the following laws:
|||
|||     Left identity: `empty <|> x = x`
|||     Right identity: `x <|> empty = x`
|||     Annihilation: `f <$> empty = empty`
|||
public export
interface Alt f => Plus f where
  constructor MkPlus
  empty : f a

||| The Alternative interface has no members of its own;
||| it just specifies that the type constructor has both
||| `Applicative` and `Plus` implementations.
|||
||| Types which have `Alternative` implementations
||| should also satisfy the following laws:
|||
|||     Distributivity: `(f <|> g) <*> x = (f <*> x) <|> (g <*> x)`
|||     Annihilation: `empty <*> f = empty`
|||
public export
interface Plus f => Applicative f => Alternative f where
  constructor MkAlternative

||| `guard a` is `pure ()` if `a` is `True` and `empty` if `a` is `False`.
public export
guard : Alternative f => Bool -> f ()
guard x = if x then pure () else empty

namespace Lazy
  public export
  [SemigroupAlt] Alt f => Semigroup (Lazy (f a)) where
    x <+> y = force x <|> y

  public export
  [MonoidPlus] Plus f => Monoid (Lazy (f a)) using Lazy.SemigroupAlt where
    neutral = delay empty

public export
[SemigroupAlt] Alt f => Semigroup (f a) where
  x <+> y = x <|> delay y

public export
[MonoidPlus] Plus f => Monoid (f a) using Interfaces.SemigroupAlt where
  neutral = empty

---------------------------------------------------------
-- FOLDABLE, FOLDABLE1, TRAVERSABLE, TRAVERSABLE1
---------------------------------------------------------

||| The `Foldable` interface describes how you can iterate over the elements in
||| a parameterised type and combine the elements together, using a provided
||| function, into a single result.
||| @ t The type of the 'Foldable' parameterised type.
public export
interface Foldable t where
  constructor MkFoldable
  ||| Successively combine the elements in a parameterised type using the
  ||| provided function, starting with the element that is in the final position
  ||| i.e. the right-most position.
  ||| @ func  The function used to 'fold' an element into the accumulated result
  ||| @ init  The starting value the results are being combined into
  ||| @ input The parameterised type
  foldr : (func : elem -> acc -> acc) -> (init : acc) -> (input : t elem) -> acc

  ||| The same as `foldr` but begins the folding from the element at the initial
  ||| position in the data structure i.e. the left-most position.
  ||| @ func  The function used to 'fold' an element into the accumulated result
  ||| @ init  The starting value the results are being combined into
  ||| @ input The parameterised type
  foldl : (func : acc -> elem -> acc) -> (init : acc) -> (input : t elem) -> acc
  foldl f z t = foldr (flip (.) . flip f) id t z

  ||| Test whether the structure is empty.
  ||| @ acc The accumulator value which is specified to be lazy
  null : t elem -> Lazy Bool
  null = foldr {acc = Lazy Bool} (\ _,_ => False) True

  ||| Similar to `foldl`, but uses a function wrapping its result in a `Monad`.
  ||| Consequently, the final value is wrapped in the same `Monad`.
  foldlM : Monad m => (funcM : acc -> elem -> m acc) -> (init : acc) -> (input : t elem) -> m acc
  foldlM fm a0 = foldl (\ma, b => ma >>= flip fm b) (pure a0)

  ||| Produce a list of the elements contained in the parametrised type.
  toList : t elem -> List elem
  toList = foldr (::) []

  ||| Maps each element to a value and combine them.
  ||| For performance reasons, this should wherever
  ||| be implemented with tail recursion.
  ||| @ f The function to apply to each element.
  foldMap : Monoid m => (f : a -> m) -> t a -> m
  foldMap f = foldr ((<+>) . f) neutral

||| Combine each element of a structure into a monoid.
public export
concat : (Foldable t, Monoid a) => t a -> a
concat = foldMap id

||| Combine into a monoid the collective results of applying a function to each
||| element of a structure.
public export
concatMap : (Foldable t, Monoid m) => (a -> m) -> t a -> m
concatMap = foldMap

namespace Bool.Lazy
  namespace Semigroup
    public export
    [Any] Semigroup (Lazy Bool) where
      x <+> y = force x || y

    public export
    [All] Semigroup (Lazy Bool) where
      x <+> y = force x && y

  namespace Monoid
    public export
    [Any] Monoid (Lazy Bool) using Semigroup.Any where
      neutral = delay False

    public export
    [All] Monoid (Lazy Bool) using Semigroup.All where
      neutral = delay True

||| The conjunction of all elements of a structure containing lazy boolean
||| values.  `and` short-circuits from left to right, evaluating until either an
||| element is `False` or no elements remain.
public export
and : Foldable t => t (Lazy Bool) -> Bool
and = force . concat @{(%search, All)}

||| The disjunction of all elements of a structure containing lazy boolean
||| values.  `or` short-circuits from left to right, evaluating either until an
||| element is `True` or no elements remain.
public export
or : Foldable t => t (Lazy Bool) -> Bool
or = force . concat @{(%search, Any)}

namespace Bool
  namespace Semigroup
    public export
    [Any] Semigroup Bool where
      x <+> y = x || delay y

    public export
    [All] Semigroup Bool where
      x <+> y = x && delay y

  namespace Monoid
    public export
    [Any] Monoid Bool using Bool.Semigroup.Any where
      neutral = False

    public export
    [All] Monoid Bool using Bool.Semigroup.All where
      neutral = True

||| The disjunction of the collective results of applying a predicate to all
||| elements of a structure.  `any` short-circuits from left to right.
public export
any : Foldable t => (a -> Bool) -> t a -> Bool
any = foldMap @{%search} @{Any}

||| The disjunction of the collective results of applying a predicate to all
||| elements of a structure.  `all` short-circuits from left to right.
public export
all : Foldable t => (a -> Bool) -> t a -> Bool
all = foldMap @{%search} @{All}
  where
    monoid : Monoid Bool
    monoid = MkMonoid @{MkSemigroup (\x, y => x && y)} True

namespace Num
  namespace Semigroup
    public export
    [Additive] Num a => Semigroup a where
      (<+>) = (+)

    public export
    [Multiplicative] Num a => Semigroup a where
      (<+>) = (*)

  namespace Monoid
    public export
    [Additive] Num a => Monoid a using Semigroup.Additive where
      neutral = 0

    public export
    [Multiplicative] Num a => Monoid a using Semigroup.Multiplicative where
      neutral = 1

||| Add together all the elements of a structure.
public export
sum : (Foldable t, Num a) => t a -> a
sum = concat @{(%search, Additive)}

||| Add together all the elements of a structure.
||| Same as `sum` but tail recursive.
export
sum' : (Foldable t, Num a) => t a -> a
sum' = sum

||| Multiply together all elements of a structure.
public export
product : (Foldable t, Num a) => t a -> a
product = concat @{(%search, Multiplicative)}

||| Multiply together all elements of a structure.
||| Same as `product` but tail recursive.
export
product' : (Foldable t, Num a) => t a -> a
product' = product

||| Map each element of a structure to a computation, evaluate those
||| computations and discard the results.
public export
traverse_ : (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr ((*>) . f) (pure ())

||| Evaluate each computation in a structure and discard the results.
public export
sequence_ : (Foldable t, Applicative f) => t (f a) -> f ()
sequence_ = foldr (*>) (pure ())

||| Like `traverse_` but with the arguments flipped.
public export
for_ : (Foldable t, Applicative f) => t a -> (a -> f b) -> f ()
for_ = flip traverse_

namespace Foldable
  ||| Composition of foldables is foldable.
  public export
  [Compose] (Foldable t, Foldable f) => Foldable (t . f) where
    foldr = foldr . flip . foldr
    foldl = foldl . foldl
    null tf = null tf || all (force . null) tf
    foldMap = foldMap . foldMap

||| Fold using Plus.
|||
||| If you have a left-biased alternative operator `<|>`, then `choice` performs
||| left-biased choice from a list of alternatives, which means that it
||| evaluates to the left-most non-`empty` alternative.
|||
||| If the list is empty, or all values in it are `empty`, then it evaluates to
||| `empty`.
|||
||| Example:
|||
||| ```
||| -- given a parser expression like:
||| expr = literal <|> keyword <|> funcall
|||
||| -- choice lets you write this as:
||| expr = choice [literal, keyword, funcall]
||| ```
|||
||| Note: In Haskell, `choice` is called `asum`.
public export
choice : (Foldable t, Plus f) => t (Lazy (f a)) -> f a
choice = force . concat @{(%search, Lazy.MonoidPlus)}

||| A fused version of `choice` and `map`.
public export
choiceMap : (Foldable t, Plus f) => (a -> f b) -> t a -> f b
choiceMap = foldMap @{%search} @{Interfaces.MonoidPlus}

||| Like `Foldable` but for non-empty data structures.
|||
||| In general this means that we only need a `Semigroup` to
||| accumulate the values stored in a data structure, while in
||| the case of `Foldable` we need a `Monoid`.
|||
||| @ t The type of the 'Foldable' parameterised type.
public export
interface Foldable t => Foldable1 t where
  constructor MkFoldable1
  foldMap1 : Semigroup m => (a -> m) -> t a -> m

||| Combine each element of a non-empty structure into a semigroup.
public export
concat1 : (Foldable1 t, Semigroup a) => t a -> a
concat1 = foldMap1 id

public export
choice1 : (Foldable1 t, Alt f) => t (Lazy (f a)) -> f a
choice1 = force . concat1 @{(%search, Lazy.SemigroupAlt)}

public export
interface (Functor t, Foldable t) => Traversable t where
  constructor MkTraversable
  ||| Map each element of a structure to a computation, evaluate those
  ||| computations and combine the results.
  traverse : Applicative f => (a -> f b) -> t a -> f (t b)

||| Evaluate each computation in a structure and collect the results.
public export
sequence : (Traversable t, Applicative f) => t (f a) -> f (t a)
sequence = traverse id

||| Like `traverse` but with the arguments flipped.
public export
for : (Traversable t, Applicative f) => t a -> (a -> f b) -> f (t b)
for = flip traverse

namespace Traversable
  ||| Composition of traversables is traversable.
  public export
  [Compose] (Traversable t, Traversable f) => Traversable (t . f)
    using Foldable.Compose Functor.Compose where
      traverse = traverse . traverse

||| Like `Traversable` but for non-empty data structures.
||| This allows us to traverse a data structure with
||| an effect that has only a `Bind` instance, while with
||| `Traversable` we need an `Applicative` effect.
public export
interface (Foldable1 t, Traversable t) => Traversable1 t where
  constructor MkTraversable1
  ||| Map each element of a non-empty structure
  ||| to a computation, evaluate those
  ||| computations and combine the results.
  traverse1 : Apply f => (a -> f b) -> t a -> f (t b)

namespace Bind
  ||| Composition of a traversable bind and bind is a bind.
  public export
  [Compose] (Bind m, Bind t, Traversable1 t) => Bind (m . t)
    using Apply.Compose where
      a >>= f = a >>= map join . traverse1 f

namespace Monad
  ||| Composition of a traversable monad and a monad is a monad.
  public export
  [ComposeBind] (Monad m, Monad t, Traversable t) => Bind (m . t)
    using Applicative.Compose where
      a >>= f = a >>= map join . traverse f

  ||| Composition of a traversable monad and a monad is a monad.
  public export
  [Compose] (Monad m, Monad t, Traversable t) => Monad (m . t)
    using Applicative.Compose Monad.ComposeBind where

---------------------------------------------------------
-- BIFUNCTOR, BIFOLDABLE, BITRAVERSABLE
---------------------------------------------------------

||| Bifunctors
||| @f The action of the Bifunctor on pairs of objects
public export
interface Bifunctor f where
  constructor MkBifunctor
  ||| The action of the Bifunctor on pairs of morphisms
  |||
  ||| ````idris example
  ||| bimap (\x => x + 1) reverse (1, "hello") == (2, "olleh")
  ||| ````
  |||
  bimap : (a -> c) -> (b -> d) -> f a b -> f c d
  bimap f g = mapFst f . mapSnd g

  ||| The action of the Bifunctor on morphisms pertaining to the first object
  |||
  ||| ````idris example
  ||| mapFst (\x => x + 1) (1, "hello") == (2, "hello")
  ||| ````
  |||
  mapFst : (a -> c) -> f a b -> f c b
  mapFst f = bimap f id

  ||| The action of the Bifunctor on morphisms pertaining to the second object
  |||
  ||| ````idris example
  ||| mapSnd reverse (1, "hello") == (1, "olleh")
  ||| ````
  |||
  mapSnd : (b -> d) -> f a b -> f a d
  mapSnd = bimap id

public export
mapHom : Bifunctor f => (a -> b) -> f a a -> f b b
mapHom f = bimap f f

||| `Bifoldable` identifies foldable structures with two different varieties
||| of elements (as opposed to `Foldable`, which has one variety of element).
||| Common examples are `Either` and `Pair`.
public export
interface Bifoldable p where
  constructor MkBifoldable
  bifoldr : (a -> acc -> acc) -> (b -> acc -> acc) -> acc -> p a b -> acc

  bifoldl : (acc -> a -> acc) -> (acc -> b -> acc) -> acc -> p a b -> acc
  bifoldl f g z t = bifoldr (flip (.) . flip f) (flip (.) . flip g) id t z

  binull : p a b -> Lazy Bool
  binull = bifoldr {acc = Lazy Bool} (\ _,_ => False) (\ _,_ => False) True

||| `Bifoldable1` identifies non-empty foldable structures with two different varieties
||| of elements (as opposed to `Foldable1`, which has one variety of element).
public export
interface Bifoldable1 p where
  constructor MkBifoldable1
  bifoldMap1 : Semigroup m => (a -> m) -> (b -> m) -> p a b -> m

public export
interface (Bifunctor p, Bifoldable p) => Bitraversable p where
  constructor MkBitraversable
  ||| Map each element of a structure to a computation, evaluate those
  ||| computations and combine the results.
  bitraverse : Applicative f => (a -> f c) -> (b -> f d) -> p a b -> f (p c d)

||| Evaluate each computation in a structure and collect the results.
public export
bisequence : (Bitraversable p, Applicative f) => p (f a) (f b) -> f (p a b)
bisequence = bitraverse id id

||| Like `bitraverse` but with the arguments flipped.
public export
bifor :  (Bitraversable p, Applicative f)
      => p a b
      -> (a -> f c)
      -> (b -> f d)
      -> f (p c d)
bifor t f g = bitraverse f g t

public export
interface Bitraversable p => Bifoldable1 p => Bitraversable1 p where
  constructor MkBitraversable1
  ||| Map each element of a non-empty structure to a computation, evaluate those
  ||| computations and combine the results.
  bitraverse1 : Apply f => (a -> f c) -> (b -> f d) -> p a b -> f (p c d)
