module Libraries.Data.List.Lazy

%default total

-- All functions here are public export
-- because their definitions are pretty much the specification.

public export
data LazyList : Type -> Type where
  Nil : LazyList a
  (::) : (1 x : a) -> (1 xs : Lazy (LazyList a)) -> LazyList a

public export
(++) : LazyList a -> Lazy (LazyList a) -> LazyList a
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

--- Interface implementations ---

public export
Semigroup (LazyList a) where
  [] <+> ys = ys
  (x :: xs) <+> ys = x :: (xs <+> ys)

public export
Monoid (LazyList a) where
  neutral = []

public export
Foldable LazyList where
  foldr op nil [] = nil
  foldr op nil (x :: xs) = x `op` foldr op nil xs

  foldl op acc [] = acc
  foldl op acc (x :: xs) = foldl op (acc `op` x) xs

  null []     = True
  null (_::_) = False

public export
Functor LazyList where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

-- There is no Traversable instance for lazy lists.
-- The result of a traversal will be a non-lazy list in general
-- (you can't delay the "effect" of an applicative functor).
public export
traverse : Applicative f => (a -> f b) -> LazyList a -> f (List b)
traverse g [] = pure []
traverse g (x :: xs) = [| g x :: traverse g xs |]

public export
sequence : Applicative f => LazyList (f a) -> f (List a)
sequence = traverse id

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

export
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
