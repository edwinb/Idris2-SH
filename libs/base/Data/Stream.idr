module Data.Stream

import Data.List
import Data.List1
import public Data.Zippable

%default total

||| Drop the first n elements from the stream
||| @ n how many elements to drop
public export
drop : (n : Nat) -> Stream a -> Stream a
drop Z     xs = xs
drop (S k) (x::xs) = drop k xs

||| An infinite stream of repetitions of the same thing
public export
repeat : a -> Stream a
repeat x = x :: repeat x

||| Generate an infinite stream by repeatedly applying a function
||| @ f the function to iterate
||| @ x the initial value that will be the head of the stream
public export
iterate : (f : a -> a) -> (x : a) -> Stream a
iterate f x = x :: iterate f (f x)

public export
unfoldr : (b -> (a, b)) -> b -> Stream a
unfoldr f c = let (a, n) = f c in a :: unfoldr f n

||| All of the natural numbers, in order
public export
nats : Stream Nat
nats = iterate S Z

||| Get the nth element of a stream
public export
index : Nat -> Stream a -> a
index Z     (x::xs) = x
index (S k) (x::xs) = index k xs

---------------------------
-- Zippable --
---------------------------

public export
Zippable Stream where
  zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

  zipWith3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: zipWith3 f xs ys zs

  unzipWith f xs = unzip (map f xs)

  unzip xs = (map fst xs, map snd xs)

  unzipWith3 f xs = unzip3 (map f xs)

  unzip3 xs = (map (\(x, _, _) => x) xs, map (\(_, x, _) => x) xs, map (\(_, _, x) => x) xs)

export
zipWithIndexLinear : (0 f : _) -> (xs, ys : Stream a) -> (i : Nat) -> index i (zipWith f xs ys) = f (index i xs) (index i ys)
zipWithIndexLinear f (_::xs) (_::ys) Z     = Refl
zipWithIndexLinear f (_::xs) (_::ys) (S k) = zipWithIndexLinear f xs ys k

export
zipWith3IndexLinear : (0 f : _) -> (xs, ys, zs : Stream a) -> (i : Nat) -> index i (zipWith3 f xs ys zs) = f (index i xs) (index i ys) (index i zs)
zipWith3IndexLinear f (_::xs) (_::ys) (_::zs) Z     = Refl
zipWith3IndexLinear f (_::xs) (_::ys) (_::zs) (S k) = zipWith3IndexLinear f xs ys zs k

||| Return the diagonal elements of a stream of streams
export
diag : Stream (Stream a) -> Stream a
diag ((x::xs)::xss) = x :: diag (map tail xss)

||| Produce a Stream of left folds of prefixes of the given Stream
||| @ f the combining function
||| @ acc the initial value
||| @ xs the Stream to process
export
scanl : (f : a -> b -> a) -> (acc : a) -> (xs : Stream b) -> Stream a
scanl f acc (x :: xs) = acc :: scanl f (f acc x) xs

||| Produce a Stream repeating a sequence
||| @ xs the sequence to repeat
||| @ ok proof that the list is non-empty
export
cycle : (xs : List a) -> {auto 0 ok : NonEmpty xs} -> Stream a
cycle (x :: xs) = x :: cycle' xs
  where cycle' : List a -> Stream a
        cycle' []        = x :: cycle' xs
        cycle' (y :: ys) = y :: cycle' ys

--------------------------------------------------------------------------------
-- Interleavings
--------------------------------------------------------------------------------

-- zig, zag, and cantor are taken from the paper
-- Applications of Applicative Proof Search
-- by Liam O'Connor

public export
zig : List1 (Stream a) -> Stream (Stream a) -> Stream a

public export
zag : List1 a -> List1 (Stream a) -> Stream (Stream a) -> Stream a

zig xs = zag (head <$> xs) (tail <$> xs)

zag (x ::: []) zs (l :: ls) = x :: zig (l ::: forget zs) ls
zag (x ::: (y :: xs)) zs ls = x :: zag (y ::: xs) zs ls

public export
cantor : Stream (Stream a) -> Stream a
cantor (l :: ls) = zig (l ::: []) ls

-- Exploring the Nat*Nat top right quadrant of the plane
-- using Cantor's zig-zag traversal:
example :
  let quadrant : Stream (Stream (Nat, Nat))
      quadrant = map (\ i => map (i,) Stream.nats) Stream.nats
  in
     take 10 (cantor quadrant)
     === [ (0, 0)
         , (1, 0), (0, 1)
         , (2, 0), (1, 1), (0, 2)
         , (3, 0), (2, 1), (1, 2), (0, 3)
         ]
example = Refl

namespace DPair

  ||| Explore the plane corresponding to all possible pairings
  ||| using Cantor's zig zag traversal
  public export
  planeWith : {0 p : a -> Type} ->
              ((x : a) -> p x -> c) ->
              Stream a -> ((x : a) -> Stream (p x)) ->
              Stream c
  planeWith k as f = cantor (map (\ x => map (k x) (f x)) as)

  ||| Explore the plane corresponding to all possible pairings
  ||| using Cantor's zig zag traversal
  public export
  plane : {0 p : a -> Type} ->
          Stream a -> ((x : a) -> Stream (p x)) ->
          Stream (x : a ** p x)
  plane = planeWith (\ x, prf => (x ** prf))

namespace Pair

  ||| Explore the plane corresponding to all possible pairings
  ||| using Cantor's zig zag traversal
  public export
  planeWith : (a -> b -> c) ->
              Stream a -> (a -> Stream b) ->
              Stream c
  planeWith k as f = cantor (map (\ x => map (k x) (f x)) as)

  ||| Explore the plane corresponding to all possible pairings
  ||| using Cantor's zig zag traversal
  public export
  plane : Stream a -> (a -> Stream b) -> Stream (a, b)
  plane = Pair.planeWith (,)

--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

export
Apply Stream where
  (<*>) = zipWith apply

export
Applicative Stream where
  pure = repeat

export
Bind Stream where
  s >>= f = diag (map f s)

export
Monad Stream where

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

lengthTake : (n : Nat) -> (xs : Stream a) -> length (take n xs) = n
lengthTake Z _ = Refl
lengthTake (S n) (x :: xs) = cong S (lengthTake n xs)
