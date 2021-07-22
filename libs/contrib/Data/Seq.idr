||| General purpose two-end finite sequences, 
||| with length in its type.
|||
||| This is implemented by finger tree.
module Data.Seq

import public Data.Fin
import public Data.Nat
import public Data.Vect
import public Data.Zippable

import Data.Seq.Internal

%default total

err : String -> a
err s = assert_total (idris_crash s)

||| A two-end finite sequences, with length in its type.
export
data Seq : Nat -> Type -> Type where
  MkSeq : FingerTree (Elem e) -> Seq n e

||| O(1). The empty sequence.
export
empty : Seq 0 e
empty = MkSeq Empty

||| O(1). A singleton sequence.
export
singleton : e -> Seq 1 e
singleton a = MkSeq (Single (MkElem a))

||| O(n). A sequence of length n with a the value of every element.
export
replicate : (n : Nat) -> (a : e) -> Seq n e
replicate n a = MkSeq (replicate' n a)    

||| O(1). The number of elements in the sequence.
export
length : {n : Nat} -> Seq n a -> Nat
length _ = n

||| O(n). Reverse the sequence.
export
reverse : Seq n a -> Seq n a
reverse (MkSeq tr) = MkSeq (reverseTree id tr)

infixr 5 `cons`
||| O(1). Add an element to the left end of a sequence.
export
cons : e -> Seq n e -> Seq (S n) e
a `cons` MkSeq tr = MkSeq (MkElem a `consTree` tr)

infixl 5 `snoc`
||| O(1). Add an element to the right end of a sequence.
export
snoc : Seq n e -> e -> Seq (S n) e
MkSeq tr `snoc` a = MkSeq (tr `snocTree` MkElem a)

||| O(log(min(m, n))). Concatenate two sequences.
export
(++) : Seq m e -> Seq n e -> Seq (m + n) e
MkSeq t1 ++ MkSeq t2 = MkSeq (addTree0 t1 t2)

||| O(1). View from the left of the sequence.
export
viewl : Seq (S n) a -> (a, Seq n a)
viewl (MkSeq tr) = case viewLTree tr of
  Just (MkElem a, tr') => (a, MkSeq tr')
  Nothing              => err "viewl"

||| O(1). The first element of the sequence.
export
head : Seq (S n) a -> a
head = fst . viewl

||| O(1). The elements after the head of the sequence.
export
tail : Seq (S n) a -> Seq n a
tail = snd . viewl

||| O(1). View from the right of the sequence.
export
viewr : Seq (S n) a -> (Seq n a, a)
viewr (MkSeq tr) = case viewRTree tr of
  Just (tr', MkElem a) => (MkSeq tr', a)
  Nothing              => err "viewr"

||| O(1). The elements before the last element of the sequence.
export
init : Seq (S n) a -> Seq n a
init = fst . viewr

||| O(1). The last element of the sequence.
export
last : Seq (S n) a -> a
last = snd . viewr

||| O(n). Turn a vector into a sequence.
export
fromVect : Vect n a -> Seq n a
fromVect xs = MkSeq (foldr (\x, t => MkElem x `consTree` t) Empty xs)

||| O(n). Turn a list into a sequence.
export
fromList : (xs : List a) -> Seq (length xs) a
fromList xs = fromVect (Vect.fromList xs)

||| O(n). Turn a sequence into a vector.
export
toVect : {n :Nat} -> Seq n a -> Vect n a
toVect _  {n = 0}   = []
toVect ft {n = S _} = 
  let (x, ft') = viewl ft
  in x :: toVect ft'

||| O(log(min(i, n-i))). The element at the specified position.
export
index : (i : Nat) -> (t : Seq n a) -> {auto ok : LT i n} -> a
index i (MkSeq t) = let (_, MkElem a) = lookupTree i t in a

||| O(log(min(i, n-i))). The element at the specified position.
||| Use Fin n to index instead.
export
index' : (t : Seq n a) -> (i : Fin n) -> a
index' (MkSeq t) fn = let (_, MkElem a) = lookupTree (finToNat fn) t in a

||| O(log(min(i, n-i))). Update the element at the specified position.
export
adjust : (f : a -> a) -> (i : Nat) -> (t : Seq n a) -> {auto ok : LT i n} -> Seq n a
adjust f i (MkSeq t) = MkSeq $ adjustTree (const (map f)) i t

||| O(log(min(i, n-i))). Replace the element at the specified position.
export
update : (i : Nat) -> a -> (t : Seq n a) -> {auto ok : LT i n} -> Seq n a
update i a t = adjust (const a) i t

||| O(log(min(i, n-i))). Split a sequence at a given position.
export
splitAt : (i : Nat) -> Seq n a -> {auto ok : LT i n} -> (Seq i a, Seq (n `minus` i) a)
splitAt i (MkSeq xs) = 
  let (l, r) = split i xs 
  in (MkSeq l, MkSeq r)

||| O(log(min(i, n-i))). The first i elements of a sequence.
export 
take : (i : Nat) -> Seq n a -> {auto ok : LT i n} -> Seq i a
take i seq = fst (splitAt i seq)

||| O(log(min(i, n-i))). Elements of a sequence after the first i.
export 
drop : (i : Nat) -> Seq n a -> {auto ok : LT i n} -> Seq (n `minus` i) a
drop i seq = snd (splitAt i seq)

||| Dump the internal structure of the finger tree.
export
show' : Show a => Seq n a -> String
show' (MkSeq tr) = showPrec Open tr

public export
implementation Eq a => Eq (Seq n a) where
  MkSeq x == MkSeq y = x == y

public export
implementation Ord a => Ord (Seq n a) where
  compare (MkSeq x) (MkSeq y) = compare x y

public export
implementation Functor (Seq n) where
  map f (MkSeq tr) = MkSeq (map (map f) tr)

public export
implementation Foldable (Seq n) where
  foldr f z (MkSeq tr) = foldr (f . unElem) z tr

  foldl f z (MkSeq tr) = foldl (\acc, (MkElem elem) => f acc elem) z tr

  toList (MkSeq tr) = toList' tr

  null (MkSeq Empty) = True
  null _ = False

public export
implementation Traversable (Seq n) where
  traverse f (MkSeq tr) = MkSeq <$> traverse (map MkElem . f . unElem) tr

public export
implementation Show a => Show (Seq n a) where
  showPrec p = showPrec p . toList

public export
implementation Zippable (Seq n) where
  zipWith f (MkSeq x) (MkSeq y) = MkSeq (zipWith' f x y)

  zipWith3 f (MkSeq x) (MkSeq y) (MkSeq z) = MkSeq (zipWith3' f x y z) 

  unzipWith f (MkSeq zs) = let (xs, ys) = unzipWith' f zs in (MkSeq xs, MkSeq ys)
      
  unzipWith3 f (MkSeq ws) = let (xs, ys, zs) = unzipWith3' f ws in (MkSeq xs, MkSeq ys, MkSeq zs)

||| This implementation works like a ZipList,
||| and is differnt from that of Seq'.
public export
implementation {n : Nat} -> Applicative (Seq n) where
  pure = replicate n
  (<*>) = zipWith ($)
