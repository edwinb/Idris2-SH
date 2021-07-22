module Data.Colist

import Data.Maybe
import Data.List
import Data.List1
import public Data.Zippable

%default total

||| A possibly finite Stream.
public export
data Colist : (a : Type) -> Type where
  Nil : Colist a
  (::) : a -> Inf (Colist a) -> Colist a

--------------------------------------------------------------------------------
--          Creating Colists
--------------------------------------------------------------------------------

||| Convert a list to a `Colist`.
public export
fromList : List a -> Colist a
fromList []        = Nil
fromList (x :: xs) = x :: fromList xs

||| Convert a stream to a `Colist`.
public export
fromStream : Stream a -> Colist a
fromStream (x :: xs) = x :: fromStream xs

||| Create a `Colist` of only a single element.
public export
singleton : a -> Colist a
singleton a = a :: Nil

||| An infinite `Colist` of repetitions of the same element.
public export
repeat : a -> Colist a
repeat v = v :: repeat v

||| Create a `Colist` of `n` replications of the given element.
public export
replicate : Nat -> a -> Colist a
replicate 0     _ = Nil
replicate (S k) x = x :: replicate k x

||| Produce a `Colist` by repeating a sequence.
public export
cycle : List a -> Colist a
cycle Nil       = Nil
cycle (x :: xs) = run x xs
  where run : a -> List a -> Colist a
        run v []        = v :: run x xs
        run v (y :: ys) = v :: run y ys

||| Generate an infinite `Colist` by repeatedly applying a function.
public export
iterate : (a -> a) -> a -> Colist a
iterate f a = a :: iterate f (f a)

||| Generate a `Colist` by repeatedly applying a function.
||| This stops once the function returns `Nothing`.
public export
iterateMaybe : (f : a -> Maybe a) -> Maybe a -> Colist a
iterateMaybe _ Nothing  = Nil
iterateMaybe f (Just x) = x :: iterateMaybe f (f x)

||| Generate an `Colist` by repeatedly applying a function
||| to a seed value.
||| This stops once the function returns `Nothing`.
public export
unfold : (f : s -> Maybe (s,a)) -> s -> Colist a
unfold f s = case f s of
                  Just (s2,a) => a :: unfold f s2
                  Nothing     => Nil

--------------------------------------------------------------------------------
--          Basic Functions
--------------------------------------------------------------------------------

||| True, if this is the empty `Colist`.
public export
isNil : Colist a -> Bool
isNil [] = True
isNil _  = False

||| True, if the given `Colist` is non-empty.
public export
isCons : Colist a -> Bool
isCons [] = False
isCons _  = True

||| Concatenate two `Colist`s.
public export
append : Colist a -> Colist a -> Colist a
append []        ys = ys
append (x :: xs) ys = x :: append xs ys

||| Append a `Colist` to a `List`.
public export
lappend : List a -> Colist a -> Colist a
lappend xs = append (fromList xs)

||| Append a `List` to a `Colist`.
public export
appendl : Colist a -> List a -> Colist a
appendl xs = append xs . fromList

||| Try to extract the head and tail of a `Colist`.
public export
uncons : Colist a -> Maybe (a, Colist a)
uncons [] = Nothing
uncons (x :: xs) = Just (x, xs)

||| Try to extract the first element from a `Colist`.
public export
head : Colist a -> Maybe a
head []       = Nothing
head (x :: _) = Just x

||| Try to drop the first element from a `Colist`.
||| This returns `Nothing` if the given `Colist` is
||| empty.
public export
tail : Colist a -> Maybe (Colist a)
tail []        = Nothing
tail (_ :: xs) = Just xs

||| Take up to `n` elements from a `Colist`.
public export
take : (n : Nat) -> Colist a -> List a
take 0     _         = Nil
take (S k) []        = Nil
take (S k) (x :: xs) = x :: take k xs

||| Take elements from a `Colist` up to and including the
||| first element, for which `p` returns `True`.
public export
takeUntil : (p : a -> Bool) -> Colist a -> Colist a
takeUntil _ []        = Nil
takeUntil p (x :: xs) = if p x then [x] else x :: takeUntil p xs

||| Take elements from a `Colist` up to (but not including) the
||| first element, for which `p` returns `True`.
public export
takeBefore : (a -> Bool) -> Colist a -> Colist a
takeBefore _ []        = Nil
takeBefore p (x :: xs) = if p x then [] else x :: takeBefore p xs

||| Take elements from a `Colist` while the given predicate
||| returns `True`.
public export
takeWhile : (a -> Bool) -> Colist a -> Colist a
takeWhile p = takeBefore (not . p)

||| Extract all values wrapped in `Just` from the beginning
||| of a `Colist`. This stops, once the first `Nothing` is encountered.
public export
takeWhileJust : Colist (Maybe a) -> Colist a
takeWhileJust []              = []
takeWhileJust (Nothing :: _)  = []
takeWhileJust (Just x  :: xs) = x :: takeWhileJust xs

||| Drop up to `n` elements from the beginning of the `Colist`.
public export
drop : (n : Nat) -> Colist a -> Colist a
drop _ []            = Nil
drop 0           xs  = xs
drop (S k) (x :: xs) = drop k xs

||| Try to extract the `n`-th element from a `Colist`.
public export
index : (n : Nat) -> Colist a -> Maybe a
index _     []        = Nothing
index 0     (x :: _)  = Just x
index (S k) (_ :: xs) = index k xs

||| Produce a `Colist` of left folds of prefixes of the given `Colist`.
||| @ f the combining function
||| @ acc the initial value
||| @ xs the `Colist` to process
public export
scanl : (f : a -> b -> a) -> (acc : a) -> (xs : Colist b) -> Colist a
scanl _ acc Nil       = [acc]
scanl f acc (x :: xs) = acc :: scanl f (f acc x) xs

--------------------------------------------------------------------------------
-- InBounds and inBounds for Colists
--------------------------------------------------------------------------------

||| Satisfiable if `k` is a valid index into `xs`
|||
||| @ k the potential index
||| @ xs the Colist into which k may be an index
public export
data InBounds : (k : Nat) -> (xs : Colist a) -> Type where
    ||| Z is a valid index into any cons cell
    InFirst : {0 xs : Inf (Colist a)} -> InBounds Z (x :: xs)
    ||| Valid indices can be extended
    InLater : {0 xs : Inf (Colist a)} -> InBounds k xs -> InBounds (S k) (x :: xs)

public export
Uninhabited (Data.Colist.InBounds k []) where
  uninhabited InFirst impossible
  uninhabited (InLater _) impossible

export
Uninhabited (Colist.InBounds k xs) => Uninhabited (Colist.InBounds (S k) (x::xs)) where
  uninhabited (InLater y) = uninhabited y

||| Decide whether `k` is a valid index into Colist `xs`
public export
inBounds : (k : Nat) -> (xs : Colist a) -> Dec (InBounds k xs)
inBounds k [] = No uninhabited
inBounds Z (x::xs) = Yes InFirst
inBounds (S k) (x::xs) = case inBounds k xs of
  Yes p => Yes $ InLater p
  No up => No $ \(InLater p) => up p

||| Find a particular element of a Colist using InBounds
|||
||| @ ok a proof that the index is within bounds
public export
index' : (k : Nat) -> (xs : Colist a) -> {auto 0 ok : InBounds k xs} -> a
index' Z (x::_) {ok = InFirst} = x
index' (S k) (_::xs) {ok = InLater _} = index' k xs

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
Semigroup (Colist a) where
  (<+>) = append

public export
Monoid (Colist a) where
  neutral = Nil

public export
Functor Colist where
  map f []        = []
  map f (x :: xs) = f x :: map f xs

public export
Applicative Colist where
  pure = repeat

  [] <*> _  = []
  _  <*> [] = []
  f :: fs <*> a :: as = f a :: (fs <*> as)

public export
Zippable Colist where
  zipWith f as bs = [| f as bs |]

  zipWith3 f as bs cs = [| f as bs cs |]

  unzip xs = (map fst xs, map snd xs)

  unzip3 xs = ( map (\(a,_,_) => a) xs
              , map (\(_,b,_) => b) xs
              , map (\(_,_,c) => c) xs
              )

  unzipWith f = unzip . map f

  unzipWith3 f = unzip3 . map f
