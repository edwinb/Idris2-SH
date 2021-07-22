||| General purpose two-end finite sequences.
|||
||| This is implemented by finger tree.
module Data.Seq.Seq'

import public Data.Zippable

import Data.Seq.Internal

%default total

||| A two-end finite sequences.
export
data Seq' : Type -> Type where
  MkSeq' : FingerTree (Elem e) -> Seq' e

||| O(1). The empty sequence.
export
empty : Seq' e
empty = MkSeq' Empty

||| O(1). A singleton sequence.
export
singleton : e -> Seq' e
singleton a = MkSeq' (Single (MkElem a))

||| O(n). A sequence of length n with a the value of every element.
export
replicate : (n : Nat) -> (a : e) -> Seq' e
replicate n a = MkSeq' (replicate' n a)    

||| O(1). The number of elements in the sequence.
export
length : Seq' a -> Nat
length (MkSeq' tr) = length' tr

||| O(n). Reverse the sequence.
export
reverse : Seq' a -> Seq' a
reverse (MkSeq' tr) = MkSeq' (reverseTree id tr)

infixr 5 `cons`
||| O(1). Add an element to the left end of a sequence.
export
cons : e -> Seq' e -> Seq' e
a `cons` MkSeq' tr = MkSeq' (MkElem a `consTree` tr)

infixl 5 `snoc`
||| O(1). Add an element to the right end of a sequence.
export
snoc : Seq' e -> e -> Seq' e
MkSeq' tr `snoc` a = MkSeq' (tr `snocTree` MkElem a)

||| O(log(min(m, n))). Concatenate two sequences.
export
(++) : Seq' e -> Seq' e -> Seq' e
MkSeq' t1 ++ MkSeq' t2 = MkSeq' (addTree0 t1 t2)

||| O(1). View from the left of the sequence.
export
viewl : Seq' a -> Maybe (a, Seq' a)
viewl (MkSeq' tr) = case viewLTree tr of
  Just (MkElem a, tr') => Just (a, MkSeq' tr')
  Nothing              => Nothing

||| O(1). The first element of the sequence.
export
head : Seq' a -> Maybe a
head s = fst <$> viewl s

||| O(1). The elements after the head of the sequence.
||| Returns an empty sequence when the sequence is empty.
export
tail : Seq' a -> Seq' a
tail s = case viewl s of
  Just (_, s') => s'
  Nothing      => empty

||| O(1). View from the right of the sequence.
export
viewr : Seq' a -> Maybe (Seq' a, a)
viewr (MkSeq' tr) = case viewRTree tr of
  Just (tr', MkElem a) => Just (MkSeq' tr', a)
  Nothing              => Nothing

||| O(1). The elements before the last element of the sequence.
||| Returns an empty sequence when the sequence is empty.
export
init : Seq' a -> Seq' a
init s = case viewr s of
  Just (s', _) => s'
  Nothing      => empty

||| O(1). The last element of the sequence.
export
last : Seq' a -> Maybe a
last s = snd <$> viewr s

||| O(n). Turn a list into a sequence.
export
fromList : List a -> Seq' a
fromList xs = MkSeq' (foldr (\x, t => MkElem x `consTree` t) Empty xs)

||| O(log(min(i, n-i))). The element at the specified position.
export
index : Nat -> Seq' a -> Maybe a
index i (MkSeq' t) = if i < length' t
  then let (_, MkElem a) = lookupTree i t in Just a
  else Nothing

||| O(log(min(i, n-i))). Update the element at the specified position.
||| If the position is out of range, the original sequence is returned.
export
adjust : (a -> a) -> Nat -> Seq' a -> Seq' a
adjust f i s@(MkSeq' t) = if i < length' t
  then MkSeq' $ adjustTree (const (map f)) i t
  else s

||| O(log(min(i, n-i))). Replace the element at the specified position.
||| If the position is out of range, the original sequence is returned.
export
update : Nat -> a -> Seq' a -> Seq' a
update i a t = adjust (const a) i t

||| O(log(min(i, n-i))). Split a sequence at a given position.
||| splitAt i s = (take i s, drop i s)
export
splitAt : Nat -> Seq' a -> (Seq' a, Seq' a)
splitAt i s@(MkSeq' t) = if i < length' t
  then let (l, r) = split i t 
       in (MkSeq' l, MkSeq' r)
  else (s, empty)

||| O(log(min(i,n-i))). The first i elements of a sequence.
||| If the sequence contains fewer than i elements, the whole sequence is returned.
export 
take : Nat -> Seq' a -> Seq' a
take i seq = fst (splitAt i seq)

||| O(log(min(i,n-i))). Elements of a sequence after the first i.
||| If the sequence contains fewer than i elements, the empty sequence is returned.
export 
drop : Nat -> Seq' a -> Seq' a
drop i seq = snd (splitAt i seq)

||| Dump the internal structure of the finger tree.
export
show' : Show a => Seq' a -> String
show' (MkSeq' tr) = showPrec Open tr

public export
implementation Eq a => Eq (Seq' a) where
  MkSeq' x == MkSeq' y = x == y

public export
implementation Ord a => Ord (Seq' a) where
  compare (MkSeq' x) (MkSeq' y) = compare x y

public export
implementation Functor Seq' where
  map f (MkSeq' tr) = MkSeq' (map (map f) tr)

public export
implementation Foldable Seq' where
  foldr f z (MkSeq' tr) = foldr (f . unElem) z tr

  foldl f z (MkSeq' tr) = foldl (\acc, (MkElem elem) => f acc elem) z tr

  toList (MkSeq' tr) = toList' tr

  null (MkSeq' Empty) = True
  null _ = False

public export
implementation Traversable Seq' where
  traverse f (MkSeq' tr) = MkSeq' <$> traverse (map MkElem . f . unElem) tr

public export
implementation Show a => Show (Seq' a) where
  showPrec p = showPrec p . toList

public export
implementation Zippable Seq' where
  zipWith f (MkSeq' x) (MkSeq' y) = MkSeq' (zipWith' f x y)

  zipWith3 f (MkSeq' x) (MkSeq' y) (MkSeq' z) = MkSeq' (zipWith3' f x y z) 

  unzipWith f (MkSeq' zs) = let (xs, ys) = unzipWith' f zs in (MkSeq' xs, MkSeq' ys)
      
  unzipWith3 f (MkSeq' ws) = let (xs, ys, zs) = unzipWith3' f ws in (MkSeq' xs, MkSeq' ys, MkSeq' zs)

public export
implementation Semigroup (Seq' a) where
  (<+>) = (++)

public export
implementation Monoid (Seq' a) where
  neutral = empty

||| This implementation is differnt from that of Seq.
public export
implementation Applicative Seq' where
  pure = singleton
  fs <*> xs = foldMap (\f => map f xs) fs

public export
[ListLike] Alternative Seq' where
  empty = empty
  a <|> b = a ++ b

public export
[MaybeLike] Alternative Seq' where
  empty = empty
  MkSeq' Empty <|> b = b
  a <|> _ = a

public export
implementation Monad Seq' where
  xs >>= f = foldMap f xs
