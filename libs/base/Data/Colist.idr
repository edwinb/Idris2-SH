module Data.Colist

import Data.Maybe
import Data.List
import public Data.Zippable

%default total

||| A possibly infinite list.
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
||| This stops with `Nil` once the function returns `Nothing`.
public export
iterateMaybe : (f : a -> Maybe a) -> Maybe a -> Colist a
iterateMaybe _ Nothing  = Nil
iterateMaybe f (Just x) = x :: iterateMaybe f (f x)

||| Generate an infinite `Colist` by repeatedly applying a function
||| to a seed value.
public export
unfoldr : (f : s -> (s,a)) -> s -> Colist a
unfoldr f s = let (s2,a) = f s
               in a :: unfoldr f s2

||| Generate an `Colist` by repeatedly applying a function
||| to a seed value.
||| This stops with `Nil` once the function returns `Nothing`.
public export
unfoldrMaybe : (f : s -> Maybe (s,a)) -> s -> Colist a
unfoldrMaybe f s = case f s of
                        Just (s2,a) => a :: unfoldrMaybe f s2
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

||| Append two `Colist`s.
public export
append : Colist a -> Colist a -> Colist a
append []        ys = ys
append (x :: xs) ys = x :: append xs ys

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

||| Take elements from a `Colist` upto and including the
||| first element, for which `p` returns `True`.
public export
takeUntil : (p : a -> Bool) -> Colist a -> Colist a
takeUntil _ []        = Nil
takeUntil p (x :: xs) = if p x then [x] else x :: takeUntil p xs

||| Take elements from a `Colist` upto (but not including) the
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

||| Drop up to n elements from the beginning of the `Colist`.
public export
drop : (n : Nat) -> Colist a -> Colist a
drop _ []            = Nil
drop 0           xs  = xs
drop (S k) (x :: xs) = drop k xs

||| Try to extract the n-th element from a `Colist`.
public export
index : Nat -> Colist a -> Maybe a
index _     []        = Nothing
index 0     (x :: _)  = Just x
index (S k) (_ :: xs) = index k xs

||| Produce a `Colist` of left folds of prefixes of the given `Colist`.
||| @ f the combining function
||| @ acc the initial value
||| @ xs the `Colist1` to process
public export
scanl : (f : a -> b -> a) -> (acc : a) -> (xs : Colist b) -> Colist a
scanl _ acc Nil       = [acc]
scanl f acc (x :: xs) = acc :: scanl f (f acc x) xs

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

||| Alias for `join`.
public export
diag : Colist (Colist a) -> Colist a
diag []                = []
diag ([] :: _)         = []
diag ((x :: _) :: xss) = x :: diag (fromMaybe [] . tail <$> xss)

public export
Monad Colist where
  join = diag

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
