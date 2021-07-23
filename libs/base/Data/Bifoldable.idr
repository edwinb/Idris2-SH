||| Additional utility functions for the `Bifoldable` interface.
module Data.Bifoldable

%default total

||| Left associative monadic bifold over a structure.
public export
bifoldlM :  (Bifoldable p, Monad m)
         => (f: a -> b -> m a)
         -> (g: a -> c -> m a)
         -> (init: a)
         -> (input: p b c) -> m a
bifoldlM f g a0 = bifoldl (\ma,b => ma >>= flip f b)
                          (\ma,c => ma >>= flip g c)
                          (pure a0)

||| Combines the elements of a structure,
||| given ways of mapping them to a common monoid.
public export
bifoldMap : (Bifoldable p, Monoid m) => (a -> m) -> (b -> m) -> p a b -> m
bifoldMap f g = bifoldr ((<+>) . f) ((<+>) . g) neutral

||| Combines the elements of a structure using a monoid.
public export
biconcat : (Bifoldable p, Monoid m) => p m m -> m
biconcat = bifoldr (<+>) (<+>) neutral

||| Combines the elements of a structure,
||| given ways of mapping them to a common monoid.
public export
biconcatMap : (Bifoldable p, Monoid m) => (a -> m) -> (b -> m) -> p a b -> m
biconcatMap f g = bifoldr ((<+>) . f) ((<+>) . g) neutral

||| The conjunction of all elements of a structure containing lazy boolean
||| values.  `biand` short-circuits from left to right, evaluating until either an
||| element is `False` or no elements remain.
public export
biand : Bifoldable p => p (Lazy Bool) (Lazy Bool) -> Bool
biand = bifoldl (&&) (&&) True

||| The disjunction of all elements of a structure containing lazy boolean
||| values.  `bior` short-circuits from left to right, evaluating either until an
||| element is `True` or no elements remain.
public export
bior : Bifoldable p => p (Lazy Bool) (Lazy Bool) -> Bool
bior = bifoldl (||) (||) False

||| The disjunction of the collective results of applying a predicate to all
||| elements of a structure. `biany` short-circuits from left to right.
public export
biany : Bifoldable p => (a -> Bool) -> (b -> Bool) -> p a b -> Bool
biany f g = bifoldl (\x,y => x || f y) (\x,y => x || g y) False

||| The disjunction of the collective results of applying a predicate to all
||| elements of a structure.  `biall` short-circuits from left to right.
public export
biall : Bifoldable p => (a -> Bool) -> (b -> Bool) -> p a b -> Bool
biall f g = bifoldl (\x,y => x && f y) (\x,y => x && g y) True

||| Add together all the elements of a structure.
public export
bisum : (Bifoldable p, Num a) => p a a -> a
bisum = bifoldr (+) (+) 0

||| Add together all the elements of a structure.
||| Same as `bisum` but tail recursive.
export
bisum' : (Bifoldable p, Num a) => p a a -> a
bisum' = bifoldl (+) (+) 0

||| Multiply together all elements of a structure.
public export
biproduct : (Bifoldable p, Num a) => p a a -> a
biproduct = bifoldr (*) (*) 1

||| Multiply together all elements of a structure.
||| Same as `product` but tail recursive.
export
biproduct' : (Bifoldable p, Num a) => p a a -> a
biproduct' = bifoldl (*) (*) 1

||| Map each element of a structure to a computation, evaluate those
||| computations and discard the results.
public export
bitraverse_ :  (Bifoldable p, Applicative f)
            => (a -> f x)
            -> (b -> f y)
            -> p a b
            -> f ()
bitraverse_ f g = bifoldr ((*>) . f) ((*>) . g) (pure ())

||| Evaluate each computation in a structure and discard the results.
public export
bisequence_ : (Bifoldable p, Applicative f) => p (f a) (f b) -> f ()
bisequence_ = bifoldr (*>) (*>) (pure ())

||| Like `bitraverse_` but with the arguments flipped.
public export
bifor_ :  (Bifoldable p, Applicative f)
       => p a b
       -> (a -> f x)
       -> (b -> f y)
       -> f ()
bifor_ p f g = bitraverse_ f g p

||| Bifold using Plus.
|||
||| If you have a left-biased alternative operator `<|>`, then `choice` performs
||| left-biased choice from a list of alternatives, which means that it
||| evaluates to the left-most non-`empty` alternative.
public export
bichoice : (Bifoldable p, Plus f) => p (Lazy (f a)) (Lazy (f a)) -> f a
bichoice t = bifoldr {a = Lazy (f a)} {b = Lazy (f a)} {acc = Lazy (f a)}
                 (\ x, xs => x <|> xs)
                 (\ x, xs => x <|> xs)
                 empty
                 t

||| A fused version of `bichoice` and `bimap`.
public export
bichoiceMap : (Bifoldable p, Plus f)
            => (a -> f x)
            -> (b -> f x)
            -> p a b ->
            f x
bichoiceMap fa fb t = bifoldr {a} {b} {acc = Lazy (f x)}
                        (\e, fx => fa e <|> fx)
                        (\e, fx => fb e <|> fx)
                        empty
                        t
