module Data.List.Lazy

import Data.Fuel
import Data.Stream
import Data.Colist
import Data.Colist1

%default total

-- All functions here are public export
-- because their definitions are pretty much the specification.

public export
data LazyList : Type -> Type where
  Nil : LazyList a
  (::) : (x : a) -> (xs : Lazy (LazyList a)) -> LazyList a

--- Truly lazy functions ---

public export
foldrLazy : (func : elem -> Lazy acc -> acc) -> (init : Lazy acc) -> (input : LazyList elem) -> acc
foldrLazy _  init [] = init
foldrLazy op init (x::xs) = x `op` foldrLazy op init xs

public export
(++) : LazyList a -> Lazy (LazyList a) -> LazyList a
(++) = flip $ foldrLazy (::)

-- Specialized variant of `concatMap` with both `t` and `m` being `LazyList`.
public export
bindLazy : (a -> LazyList b) -> LazyList a -> LazyList b
bindLazy f = foldrLazy ((++) . f) []

public export
choice : Plus f => LazyList (f a) -> f a
choice = foldrLazy (<|>) empty

public export
choiceMap : Plus f => (a -> f b) -> LazyList a -> f b
choiceMap g = foldrLazy ((<|>) . g) empty

public export
any : (a -> Bool) -> LazyList a -> Bool
any p = foldrLazy ((||) . p) False

public export
all : (a -> Bool) -> LazyList a -> Bool
all p = foldrLazy ((&&) . p) True

--- Interface implementations ---

public export
Eq a => Eq (LazyList a) where
  [] == [] = True
  x :: xs == y :: ys = x == y && xs == ys
  _ == _ = False

public export
Ord a => Ord (LazyList a) where
  compare [] [] = EQ
  compare [] (x :: xs) = LT
  compare (x :: xs) [] = GT
  compare (x :: xs) (y :: ys)
     = case compare x y of
            EQ => compare xs ys
            c => c

export
Show a => Show (LazyList a) where
  show []       = "[]"
  show (h :: t) = "[" ++ show' "" h t ++ "]"
    where
      -- Idris didn't like the lazyness involved when using the
      -- same implementation as for `List`, therefore, this was
      -- adjusted to first force the head and tail of the list.
      show' : String -> a -> LazyList a -> String
      show' acc h Nil       = acc ++ show h
      show' acc h (x :: xs) = show' (acc ++ show h ++ ", ") x xs

public export
Semigroup (LazyList a) where
  xs <+> ys = xs ++ ys

public export
Monoid (LazyList a) where
  neutral = []

public export
Foldable LazyList where
  foldr op nil [] = nil
  foldr op nil (x :: xs) = x `op` foldr op nil xs

  foldl op acc [] = acc
  foldl op acc (x :: xs) = foldl op (acc `op` x) xs

  foldlM fm init xs = foldrLazy (\x, k, z => fm z x >>= k) pure xs init

  null []     = True
  null (_::_) = False

  foldMap f [] = neutral
  foldMap f (x :: xs) = f x <+> foldMap f xs

public export
Functor LazyList where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

public export
Apply LazyList where
  fs <*> vs = bindLazy (\f => map f vs) fs

public export
Applicative LazyList where
  pure x = [x]

public export
Alt LazyList where
  (<|>) = (++)

public export
Plus LazyList where
  empty = []

public export
Alternative LazyList where

public export
Bind LazyList where
  m >>= f = bindLazy f m

public export
Monad LazyList where

-- There is no Traversable instance for lazy lists.
-- The result of a traversal will be a non-lazy list in general
-- (you can't delay the "effect" of an applicative functor).
public export
traverse : Applicative f => (a -> f b) -> LazyList a -> f (List b)
traverse g [] = pure []
traverse g (x :: xs) = [| g x :: traverse g xs |]

public export %inline
for : Applicative f => LazyList a -> (a -> f b) -> f (List b)
for = flip traverse

public export
sequence : Applicative f => LazyList (f a) -> f (List a)
sequence = traverse id

public export
Zippable LazyList where
  zipWith _ [] _ = []
  zipWith _ _ [] = []
  zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

  zipWith3 _ [] _ _ = []
  zipWith3 _ _ [] _ = []
  zipWith3 _ _ _ [] = []
  zipWith3 f (x::xs) (y::ys) (z::zs) = f x y z :: zipWith3 f xs ys zs

  unzip xs = (fst <$> xs, snd <$> xs)
  unzipWith = unzip .: map

  unzip3 xs = (fst <$> xs, fst . snd <$> xs, snd . snd <$> xs)
  unzipWith3 = unzip3 .: map

--- Lists creation ---

public export
fromList : List a -> LazyList a
fromList []      = []
fromList (x::xs) = x :: fromList xs

covering
public export
iterate : (f : a -> Maybe a) -> (x : a) -> LazyList a
iterate f x = x :: case f x of
  Nothing => []
  Just y  => iterate f y

covering
public export
unfoldr : (b -> Maybe (a, b)) -> b -> LazyList a
unfoldr f c = case f c of
  Nothing     => []
  Just (a, n) => a :: unfoldr f n

public export
iterateN : Nat -> (a -> a) -> a -> LazyList a
iterateN Z     _ _ = []
iterateN (S n) f x = x :: iterateN n f (f x)

public export
replicate : (n : Nat) -> (x : a) -> LazyList a
replicate Z     _ = []
replicate (S n) x = x :: replicate n x

--- Functions acquiring parts of list ---

public export
head' : LazyList a -> Maybe a
head' []     = Nothing
head' (x::_) = Just x

public export
tail' : LazyList a -> Maybe (LazyList a)
tail' []      = Nothing
tail' (_::xs) = Just xs

--- Functions for acquiring different types of sublists ---

public export
take : Nat -> LazyList a -> LazyList a
take (S k) (x::xs) = x :: take k xs
take _ _ = []

public export
drop : Nat -> LazyList a -> LazyList a
drop Z     xs      = xs
drop (S _) []      = []
drop (S n) (_::xs) = drop n xs

public export
takeWhile : (a -> Bool) -> LazyList a -> LazyList a
takeWhile p []      = []
takeWhile p (x::xs) = if p x then x :: takeWhile p xs else []

public export
dropWhile : (a -> Bool) -> LazyList a -> LazyList a
dropWhile p []      = []
dropWhile p (x::xs) = if p x then dropWhile p xs else x::xs

public export
filter : (a -> Bool) -> LazyList a -> LazyList a
filter p []      = []
filter p (x::xs) = if p x then x :: filter p xs else filter p xs

public export
mapMaybe : (a -> Maybe b) -> LazyList a -> LazyList b
mapMaybe f []      = []
mapMaybe f (x::xs) = case f x of
  Nothing => mapMaybe f xs
  Just y  => y :: mapMaybe f xs

namespace Stream

  public export
  take : Fuel -> Stream a -> LazyList a
  take Dry _ = []
  take (More f) (x :: xs) = x :: take f xs

namespace Colist

  public export
  take : Fuel -> Colist a -> LazyList a
  take Dry _ = []
  take _ [] = []
  take (More f) (x :: xs) = x :: take f xs

namespace Colist1

  public export
  take : Fuel -> Colist1 a -> LazyList a
  take fuel as = take fuel (forget as)

--- Functions for extending lists ---

public export
mergeReplicate : a -> LazyList a -> LazyList a
mergeReplicate sep []      = []
mergeReplicate sep (y::ys) = sep :: y :: mergeReplicate sep ys

public export
intersperse : a -> LazyList a -> LazyList a
intersperse sep []      = []
intersperse sep (x::xs) = x :: mergeReplicate sep xs

public export
intercalate : (sep : LazyList a) -> (xss : LazyList (LazyList a)) -> LazyList a
intercalate sep xss = choice $ intersperse sep xss

--- Functions converting lazy lists to something ---

public export
toColist : LazyList a -> Colist a
toColist [] = []
toColist (x::xs) = x :: toColist xs
