||| This module is not intended to be imported directly.
||| Please use Data.Seq or Data.Seq.Seq' instead.
|||
||| The implementation of fingertree comes from
||| <http://hackage.haskell.org/package/containers-0.2.0.1/docs/src/Data-Sequence.html>
|||
||| The original code is under a BSD-style license, compatible with this project.
|||
||| Original Copyrights: Copyright 2004, The University Court of the University of Glasgow
|||                      (c) Ross Paterson 2005
module Data.Seq.Internal

import Data.Zippable

%default total

err : String -> a
err s = assert_total (idris_crash s)

showApp : Show a => a -> String
showApp = showPrec App

prettyShow : Prec -> String -> String
prettyShow p s = if p >= PrefixMinus
  then "(" ++ s ++ ")"
  else s

interface Sized a where
  size : a -> Nat


-- Digit
data Digit : (e : Type) -> Type where
  One : (a : e) -> Digit e
  Two : (a : e) -> (b : e) -> Digit e
  Three : (a : e) -> (b : e) -> (c : e) -> Digit e
  Four : (a : e) -> (b : e) -> (c : e) -> (d : e) -> Digit e

implementation Functor Digit where
  map f (One a) = One (f a)
  map f (Two a b) = Two (f a) (f b)
  map f (Three a b c) = Three (f a) (f b) (f c)
  map f (Four a b c d) = Four (f a) (f b) (f c) (f d)

implementation Foldable Digit where
  foldr f z (One a) = a `f` z
  foldr f z (Two a b) = a `f` (b `f` z)
  foldr f z (Three a b c) = a `f` (b `f` (c `f` z))
  foldr f z (Four a b c d) = a `f` (b `f` (c `f` (d `f` z)))

  foldl f z (One a) = z `f` a
  foldl f z (Two a b) = (z `f` a) `f` b
  foldl f z (Three a b c) = ((z `f` a) `f` b) `f` c
  foldl f z (Four a b c d) = (((z `f` a) `f` b) `f` c) `f` d

implementation Traversable Digit where
  traverse f (One a) = [|One (f a)|]
  traverse f (Two a b) = [|Two (f a) (f b)|]
  traverse f (Three a b c) = [|Three (f a) (f b) (f c)|]
  traverse f (Four a b c d) = [|Four (f a) (f b) (f c) (f d)|]

implementation Sized e => Sized (Digit e) where
  size = foldr (\a, z => size a + z) 0

implementation Show a => Show (Digit a) where
  showPrec p (One a)        = prettyShow p $ 
    "One " ++ showApp a
  showPrec p (Two a b)      = prettyShow p $ 
    "Two " ++ showApp a ++ " " ++ showApp b
  showPrec p (Three a b c)  = prettyShow p $ 
    "Three " ++ showApp a ++ " " ++ showApp b ++ " " ++ showApp c
  showPrec p (Four a b c d) = prettyShow p $ 
    "Four " ++ showApp a ++ " " ++ showApp b ++ " " ++ showApp c ++ " " ++ showApp d


-- Node
data Node : (e : Type) -> Type where
  Node2 : Nat -> (a : e) -> (b : e) -> Node e
  Node3 : Nat -> (a : e) -> (b : e) -> (c : e) -> Node e

implementation Functor Node where
  map f (Node2 s a b)   = Node2 s (f a) (f b)
  map f (Node3 s a b c) = Node3 s (f a) (f b) (f c)

implementation Foldable Node where
  foldr f z (Node2 _ a b)   = a `f` (b `f` z)
  foldr f z (Node3 _ a b c) = a `f` (b `f` (c `f` z))

  foldl f z (Node2 _ a b)   = (z `f` a) `f` b
  foldl f z (Node3 _ a b c) = ((z `f` a) `f` b) `f` c

implementation Traversable Node where
  traverse f (Node2 s a b)   = Node2 s <$> f a <*> f b
  traverse f (Node3 s a b c) = Node3 s <$> f a <*> f b <*> f c

implementation Sized e => Sized (Node e) where
  size (Node2 s _ _)   = s
  size (Node3 s _ _ _) = s

implementation Show a => Show (Node a) where
  showPrec p (Node2 _ a b)   = prettyShow p $ 
    "Node2 " ++ showApp a ++ " " ++ showApp b
  showPrec p (Node3 _ a b c) = prettyShow p $ 
    "Node3 " ++ showApp a ++ " " ++ showApp b ++ " " ++ showApp c

-- Smart Constructors
node2 : Sized e => e -> e -> Node e
node2 a b = Node2 (size a + size b) a b

node3 : Sized e => e -> e -> e -> Node e
node3 a b c = Node3 (size a + size b + size c) a b c

-- Elem
public export
data Elem a = MkElem a

export
unElem : Elem a -> a
unElem (MkElem a) = a

public export
implementation Sized (Elem a) where
  size _ = 1

public export
implementation Eq a => Eq (Elem a) where
  MkElem a == MkElem b = a == b

public export
implementation Ord a => Ord (Elem a) where
  compare (MkElem a) (MkElem b) = compare a b

public export
implementation Functor Elem where
  map f (MkElem a) = MkElem (f a)

public export
implementation Applicative Elem where
  pure = MkElem
  MkElem f <*> MkElem a = MkElem (f a)

public export
implementation Show a => Show (Elem a) where
  showPrec p (MkElem a) = showPrec p a


-- FingerTree
public export
data FingerTree : (e : Type) -> Type where
  Empty : FingerTree e
  Single : (a : e) -> FingerTree e
  Deep : Nat -> Digit e -> FingerTree (Node e) -> Digit e -> FingerTree e

public export
implementation Sized e => Sized (FingerTree e) where
  size Empty          = 0
  size (Single a)     = size a
  size (Deep s _ _ _) = s

-- Smart Constructor
deep : Sized e => Digit e -> FingerTree (Node e) -> Digit e -> FingerTree e
deep d1 st d2 = Deep (size d1 + size st + size d2) d1 st d2


-- Reversing
reverseDigit : (a -> a) -> Digit a -> Digit a
reverseDigit f (One a) = One (f a)
reverseDigit f (Two a b) = Two (f b) (f a)
reverseDigit f (Three a b c) = Three (f c) (f b) (f a)
reverseDigit f (Four a b c d) = Four (f d) (f c) (f b) (f a)

reverseNode : (a -> a) -> Node a -> Node a
reverseNode f (Node2 s a b) = Node2 s (f b) (f a)
reverseNode f (Node3 s a b c) = Node3 s (f c) (f b) (f a)

export
reverseTree : (a -> a) -> FingerTree a -> FingerTree a
reverseTree _ Empty = Empty
reverseTree f (Single x) = Single (f x)
reverseTree f (Deep s pr m sf) =
  Deep s (reverseDigit f sf)
    (reverseTree (reverseNode f) m)
    (reverseDigit f pr)


-- Looking up
lookupDigit : Sized a => Nat -> Digit a -> (Nat, a)
lookupDigit i (One a) = (i, a)
lookupDigit i (Two a b) =
  let sa = size a
  in if i < sa
    then (i, a) 
    else (i `minus` sa, b)
lookupDigit i (Three a b c) = 
  let sa  = size a
      sab = sa + size b
  in if i < sa  
    then (i, a)
    else if i < sab 
      then (i `minus` sa, b)
      else ((i `minus` sa) `minus` sab, c)
lookupDigit i (Four a b c d) = 
  let sa   = size a
      sab  = sa + size b
      sabc = sab + size c
  in if i < sab
    then if i < sa
      then (i, a)
      else (i `minus` sa, b)
    else if i < sabc
      then (i `minus` sab, c)
      else (i `minus` sabc, d)

lookupNode : Sized a => Nat -> Node a -> (Nat, a)
lookupNode i (Node2 _ a b) =
  let sa = size a
  in if i < sa
    then (i, a)
    else (i `minus` sa, b)
lookupNode i (Node3 _ a b c) =
  let sa  = size a
      sab = sa + size b
  in if i < sa
    then (i, a)
    else if i < sab
      then (i `minus` sa, b)
      else (i `minus` sab, c)

export
lookupTree : Sized a => Nat -> FingerTree a -> (Nat, a)
lookupTree _ Empty = err "lookupTree of empty tree"
lookupTree i (Single x) = (i, x)
lookupTree i (Deep _ pr m sf) = 
  let spr = size pr
      spm = spr + size m
  in if i < spr  
    then lookupDigit i pr
    else if i < spm  
      then let (i', xs) = lookupTree (i `minus` spr) m 
           in lookupNode i' xs
      else lookupDigit (i `minus` spm) sf

-- Adjusting
adjustDigit : Sized a => (Nat -> a -> a) -> Nat -> Digit a -> Digit a
adjustDigit f i (One a) = One (f i a)
adjustDigit f i (Two a b) =
  let sa = size a
  in if i < sa
    then Two (f i a) b
    else Two a (f (i `minus` sa) b)
adjustDigit f i (Three a b c) =
  let sa  = size a
      sab = sa + size b
  in if i < sa
    then Three (f i a) b c
    else if i < sab
      then Three a (f (i `minus` sa) b) c
      else Three a b (f (i `minus` sab) c)
adjustDigit f i (Four a b c d) =
  let sa   = size a
      sab  = sa + size b
      sabc = sab + size c
  in if i < sab
    then if i < sa
      then Four (f i a) b c d
      else Four a (f (i `minus` sa) b) c d
    else if i < sabc
      then Four a b (f (i `minus` sab) c) d
      else Four a b c (f (i `minus` sabc) d)

adjustNode : Sized a => (Nat -> a -> a) -> Nat -> Node a -> Node a
adjustNode f i (Node2 s a b) =
  let sa = size a
  in if i < sa
    then Node2 s (f i a) b
    else Node2 s a (f (i `minus` sa) b)
adjustNode f i (Node3 s a b c) =
  let sa  = size a
      sab = sa + size b
  in if i < sa
    then Node3 s (f i a) b c
    else if i < sab
      then Node3 s a (f (i `minus` sa) b) c
      else Node3 s a b (f (i `minus` sab) c)

export
adjustTree : Sized a => (Nat -> a -> a) -> Nat -> FingerTree a -> FingerTree a
adjustTree _ _ Empty = err "adjustTree of empty tree"
adjustTree f i (Single x) = Single (f i x)
adjustTree f i (Deep s pr m sf) = 
  let spr = size pr
      spm = spr + size m
  in if i < spr
    then Deep s (adjustDigit f i pr) m sf
    else if i < spm
      then Deep s pr (adjustTree (adjustNode f) (i `minus` spr) m) sf
      else Deep s pr m (adjustDigit f (i `minus` spm) sf)


-- Casting between types
digitToTree : Sized a => Digit a -> FingerTree a
digitToTree (One a)        = Single a
digitToTree (Two a b)      = deep (One a) Empty (One b)
digitToTree (Three a b c)  = deep (Two a b) Empty (One c)
digitToTree (Four a b c d) = deep (Two a b) Empty (Two c d)

nodeToDigit : Node e -> Digit e
nodeToDigit (Node2 _ a b)   = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c


-- Viewing
export
viewLTree  : Sized a => FingerTree a -> Maybe (a, FingerTree a)
viewLTree Empty = Nothing
viewLTree (Single a) = Just (a, Empty)
viewLTree (Deep s (One a) m sf) =
  let tr =
    case viewLTree m of
        Nothing      => digitToTree sf
        Just (b, m') => Deep (s `minus` size a) (nodeToDigit b) m' sf
  in Just (a, tr)
viewLTree (Deep s (Two a b) m sf) =
  Just (a, Deep (s `minus` size a) (One b) m sf)
viewLTree (Deep s (Three a b c) m sf) =
  Just (a, Deep (s `minus` size a) (Two b c) m sf)
viewLTree (Deep s (Four a b c d) m sf) =
  Just (a, Deep (s `minus` size a) (Three b c d) m sf)

export
viewRTree  : Sized a => FingerTree a -> Maybe (FingerTree a, a)
viewRTree Empty = Nothing
viewRTree (Single z) = Just (Empty, z)
viewRTree (Deep s pr m (One z)) = 
  let tr = 
    case viewRTree m of
        Nothing      => digitToTree pr
        Just (m', y) => Deep (s `minus` size z) pr m' (nodeToDigit y)
  in Just (tr, z)
viewRTree (Deep s pr m (Two y z)) =
  Just (Deep (s `minus` size z) pr m (One y), z)
viewRTree (Deep s pr m (Three x y z)) =
  Just (Deep (s `minus` size z) pr m (Two x y), z)
viewRTree (Deep s pr m (Four w x y z)) =
  Just (Deep (s `minus` size z) pr m (Three w x y), z)


-- Construction
infixr 5 `consTree`
export
consTree : Sized e => (r : e) -> FingerTree e -> FingerTree e
a `consTree` Empty                       = Single a
a `consTree` Single b                    = deep (One a) Empty (One b)
a `consTree` Deep s (One b) st d2        = Deep (size a + s) (Two a b) st d2
a `consTree` Deep s (Two b c) st d2      = Deep (size a + s) (Three a b c) st d2
a `consTree` Deep s (Three b c d) st d2  = Deep (size a + s) (Four a b c d) st d2
a `consTree` Deep s (Four b c d f) st d2 = Deep (size a + s) (Two a b) (node3 c d f `consTree` st) d2

infixl 5 `snocTree`
export
snocTree : Sized e => FingerTree e -> (r : e) -> FingerTree e
Empty `snocTree` a                       = Single a
Single a `snocTree` b                    = deep (One a) Empty (One b)
Deep s d1 st (One a) `snocTree` f        = Deep (s + size a) d1 st (Two a f)
Deep s d1 st (Two a b) `snocTree` f      = Deep (s + size a) d1 st (Three a b f)
Deep s d1 st (Three a b c) `snocTree` f  = Deep (s + size a) d1 st (Four a b c f)
Deep s d1 st (Four a b c d) `snocTree` f = Deep (s + size f) d1 (st `snocTree` node3 a b c) (Two d f)


-- Splitting
data Split t a = MkSplit t a t

splitDigit : Sized a => Nat -> Digit a -> Split (Maybe (Digit a)) a
splitDigit i (One a) = MkSplit Nothing a Nothing
splitDigit i (Two a b) = 
  let sa = size a
  in if i < sa
    then MkSplit Nothing a (Just (One b))
    else MkSplit (Just (One a)) b Nothing
splitDigit i (Three a b c) = 
  let sa  = size a
      sab = sa + size b
  in if i < sa
    then MkSplit Nothing a (Just (Two b c))
    else if i < sab
      then MkSplit (Just (One a)) b (Just (One c))
      else MkSplit (Just (Two a b)) c Nothing
splitDigit i (Four a b c d) = 
  let sa   = size a
      sab  = sa + size b
      sabc = sab + size c
  in if i < sab
    then if i < sa
      then MkSplit Nothing a (Just (Three b c d))
      else MkSplit (Just (One a)) b (Just (Two c d))
    else if i < sabc
      then MkSplit (Just (Two a b)) c (Just (One d))
      else MkSplit (Just (Three a b c)) d Nothing

splitNode : Sized a => Nat -> Node a -> Split (Maybe (Digit a)) a
splitNode i (Node2 _ a b) =
  let sa = size a
  in if i < sa
    then MkSplit Nothing a (Just (One b))
    else MkSplit (Just (One a)) b Nothing
splitNode i (Node3 _ a b c) =
  let sa  = size a
      sab = sa + size b
  in if i < sa
    then MkSplit Nothing a (Just (Two b c))
    else if i < sab
      then MkSplit (Just (One a)) b (Just (One c))
      else MkSplit (Just (Two a b)) c Nothing

deepL : Sized a => Maybe (Digit a) -> FingerTree (Node a) -> Digit a -> FingerTree a
deepL Nothing m sf = case viewLTree m of
  Nothing      => digitToTree sf
  Just (a, m') => Deep (size m + size sf) (nodeToDigit a) m' sf
deepL (Just pr) m sf = deep pr m sf

deepR : Sized a => Digit a -> FingerTree (Node a) -> Maybe (Digit a) -> FingerTree a
deepR pr m Nothing = case viewRTree m of
  Nothing      => digitToTree pr
  Just (m', a) => Deep (size pr + size m) pr m' (nodeToDigit a)
deepR pr m (Just sf) = deep pr m sf

splitTree : Sized a => Nat -> FingerTree a -> Split (FingerTree a) a
splitTree _ Empty = err "splitTree of empty tree"
splitTree i (Single x) = MkSplit Empty x Empty
splitTree i (Deep _ pr m sf) =
  let spr = size pr
      spm = spr + size m
      im  = i `minus` spr
  in if i < spr
    then let MkSplit l x r = splitDigit i pr
         in MkSplit (maybe Empty digitToTree l) x (deepL r m sf)
    else if i < spm
      then let MkSplit ml xs mr = splitTree im m
               MkSplit l x r = splitNode (im `minus` size ml) xs
           in MkSplit (deepR pr  ml l) x (deepL r mr sf)
      else let MkSplit l x r = splitDigit (i `minus` spm) sf
           in MkSplit (deepR pr  m  l) x (maybe Empty digitToTree r)

export
split : Nat -> FingerTree (Elem a) -> (FingerTree (Elem a), FingerTree (Elem a))
split _ Empty = (Empty, Empty)
split i xs =
  let MkSplit l x r = splitTree i xs
  in if size xs > i
    then (l, x `consTree` r)
    else (xs, Empty)


-- Concatenation
mutual
  addDigits4 : Sized e => FingerTree (Node (Node e)) -> Digit (Node e) -> Node e -> Node e -> Node e -> Node e -> Digit (Node e) -> FingerTree (Node (Node e)) -> FingerTree (Node (Node e))
  addDigits4 m1 (One a) b c d e (One f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits4 m1 (One a) b c d e (Two f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits4 m1 (One a) b c d e (Three f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (One a) b c d e (Four f g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Two a b) c d e f (One g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits4 m1 (Two a b) c d e f (Two g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (Two a b) c d e f (Three g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Three a b c) d e f g (One h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (Three a b c) d e f g (Two h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
  addDigits4 m1 (Four a b c d) e f g h (One i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Four a b c d) e f g h (Two i j) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Four a b c d) e f g h (Three i j k) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
  addDigits4 m1 (Four a b c d) e f g h (Four i j k l) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2

  appendTree4 : Sized e => FingerTree (Node e) -> Node e -> Node e -> Node e -> Node e -> FingerTree (Node e) -> FingerTree (Node e)
  appendTree4 Empty a b c d xs = a `consTree` b `consTree` c `consTree` d `consTree` xs
  appendTree4 xs a b c d Empty = xs `snocTree` a `snocTree` b `snocTree` c `snocTree` d
  appendTree4 (Single x) a b c d xs = x `consTree` a `consTree` b `consTree` c `consTree` d `consTree` xs
  appendTree4 xs a b c d (Single x) = xs `snocTree` a `snocTree` b `snocTree` c `snocTree` d `snocTree` x
  appendTree4 (Deep s1 pr1 m1 sf1) a b c d (Deep s2 pr2 m2 sf2) = Deep (s1 + size a + size b + size c + size d + s2) pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2

  addDigits3 : Sized e => FingerTree (Node (Node e)) -> Digit (Node e) -> Node e -> Node e -> Node e -> Digit (Node e) -> FingerTree (Node (Node e)) -> FingerTree (Node (Node e))
  addDigits3 m1 (One a) b c d (One e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits3 m1 (One a) b c d (Two e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits3 m1 (One a) b c d (Three e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (One a) b c d (Four e f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Two a b) c d e (One f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits3 m1 (Two a b) c d e (Two f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (Two a b) c d e (Three f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Two a b) c d e (Four f g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Three a b c) d e f (One g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (Three a b c) d e f (Two g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Three a b c) d e f (Three g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits3 m1 (Four a b c d) e f g (One h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Four a b c d) e f g (Two h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2

  appendTree3 : Sized e => FingerTree (Node e) -> Node e -> Node e -> Node e -> FingerTree (Node e) -> FingerTree (Node e)
  appendTree3 Empty a b c xs = a `consTree` b `consTree` c `consTree` xs
  appendTree3 xs a b c Empty = xs `snocTree` a `snocTree` b `snocTree` c
  appendTree3 (Single x) a b c xs = x `consTree` a `consTree` b `consTree` c `consTree` xs
  appendTree3 xs a b c (Single x) = xs `snocTree` a `snocTree` b `snocTree` c `snocTree` x
  appendTree3 (Deep s1 pr1 m1 sf1) a b c (Deep s2 pr2 m2 sf2) = Deep (s1 + size a + size b + size c + s2) pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2

  addDigits2 : Sized e => FingerTree (Node (Node e)) -> Digit (Node e) -> Node e -> Node e -> Digit (Node e) -> FingerTree (Node (Node e)) -> FingerTree (Node (Node e))
  addDigits2 m1 (One a) b c (One d) m2 = appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits2 m1 (One a) b c (Two d e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits2 m1 (One a) b c (Three d e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (One a) b c (Four d e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Two a b) c d (One e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits2 m1 (Two a b) c d (Two e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (Two a b) c d (Three e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Two a b) c d (Four e f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Three a b c) d e (One f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (Three a b c) d e (Two f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Three a b c) d e (Three f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Three a b c) d e (Four f g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits2 m1 (Four a b c d) e f (One g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Four a b c d) e f (Two g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Four a b c d) e f (Three g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 = appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2

  appendTree2 : Sized e => FingerTree (Node e) -> Node e -> Node e -> FingerTree (Node e) -> FingerTree (Node e)
  appendTree2 Empty a b xs = a `consTree` b `consTree` xs
  appendTree2 xs a b Empty = xs `snocTree` a `snocTree` b
  appendTree2 (Single x) a b xs = x `consTree` a `consTree` b `consTree` xs
  appendTree2 xs a b (Single x) = xs `snocTree` a `snocTree` b `snocTree` x
  appendTree2 (Deep s1 pr1 m1 sf1) a b (Deep s2 pr2 m2 sf2) = Deep (s1 + size a + size b + s2) pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2

mutual
  addDigits1 : Sized e => FingerTree (Node (Node e)) -> Digit (Node e) -> Node e -> Digit (Node e) -> FingerTree (Node (Node e)) -> FingerTree (Node (Node e))
  addDigits1 m1 (One a) b (One c) m2 = appendTree1 m1 (node3 a b c) m2
  addDigits1 m1 (One a) b (Two c d) m2 = appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits1 m1 (One a) b (Three c d e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (One a) b (Four c d e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Two a b) c (One d) m2 = appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits1 m1 (Two a b) c (Two d e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (Two a b) c (Three d e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Two a b) c (Four d e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Three a b c) d (One e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (Three a b c) d (Two e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Three a b c) d (Three e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Three a b c) d (Four e f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits1 m1 (Four a b c d) e (One f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Four a b c d) e (Two f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Four a b c d) e (Three f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits1 m1 (Four a b c d) e (Four f g h i) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2

  appendTree1 : Sized e => FingerTree (Node e) -> Node e -> FingerTree (Node e) -> FingerTree (Node e)
  appendTree1 Empty a xs = a `consTree` xs
  appendTree1 xs a Empty = xs `snocTree` a
  appendTree1 (Single x) a xs = x `consTree` a `consTree` xs
  appendTree1 xs a (Single x) = xs `snocTree` a `snocTree` x
  appendTree1 (Deep s1 pr1 m1 sf1) a (Deep s2 pr2 m2 sf2) = Deep (s1 + size a + s2) pr1 (addDigits1 m1 sf1 a pr2 m2) sf2

addDigits0 : FingerTree (Node (Elem a)) -> Digit (Elem a) -> Digit (Elem a) -> FingerTree (Node (Elem a)) -> FingerTree (Node (Elem a))
addDigits0 m1 (One a) (One b) m2 = appendTree1 m1 (node2 a b) m2
addDigits0 m1 (One a) (Two b c) m2 = appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (One a) (Three b c d) m2 = appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (One a) (Four b c d e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (One c) m2 = appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (Two a b) (Two c d) m2 = appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Two a b) (Three c d e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (Four c d e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (One d) m2 = appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Three a b c) (Two d e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Three a b c) (Three d e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (Four d e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (One e) m2 = appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Four a b c d) (Two e f) m2 = appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Four a b c d) (Three e f g) m2 = appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (Four e f g h) m2 = appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2

export
addTree0 : FingerTree (Elem a) -> FingerTree (Elem a) -> FingerTree (Elem a)
addTree0 Empty xs = xs
addTree0 xs Empty = xs
addTree0 (Single x) xs = x `consTree` xs
addTree0 xs (Single x) = xs `snocTree` x
addTree0 (Deep s1 pr1 m1 sf1) (Deep s2 pr2 m2 sf2) = Deep (s1 + s2) pr1 (addDigits0 m1 sf1 pr2 m2) sf2

-- List-like
export
toList' : FingerTree (Elem a) -> List a
toList' tr = case viewLTree tr of
    Just (MkElem a, tr') => a :: assert_total (toList' tr')
    Nothing              => Nil

export
replicate' : Nat -> e -> FingerTree (Elem e)
replicate' n a = replicate1 n Empty
  where
    elem : Elem e
    elem = MkElem a
    replicate1 : Nat -> FingerTree (Elem e) -> FingerTree (Elem e)
    replicate1 Z tr = tr
    replicate1 (S k) tr = replicate1 k (elem `consTree` tr)

export
length' : FingerTree (Elem e) -> Nat
length' = size

-- FingerTree Implementations
public export
implementation Functor FingerTree where
  map _ Empty = Empty
  map f (Single x) = Single (f x)
  map f (Deep s d1 st d2) =
    Deep s (map f d1) (map (map f) st) (map f d2)

public export
implementation Foldable FingerTree where
  foldr _ z Empty            = z
  foldr f z (Single x)       = x `f` z
  foldr f z (Deep _ pr m sf) = foldr f (foldr (flip (foldr f)) (foldr f z sf) m) pr

  foldl _ z Empty            = z
  foldl f z (Single x)       = z `f` x
  foldl f z (Deep _ pr m sf) = foldl f (foldl (foldl f) (foldl f z pr) m) sf

public export
implementation Traversable FingerTree where
  traverse _ Empty            = pure Empty
  traverse f (Single x)       = Single <$> f x
  traverse f (Deep v pr m sf) =
    Deep v <$> traverse f pr <*> traverse (traverse f) m <*> traverse f sf

public export
implementation Show a => Show (FingerTree a) where
  showPrec _ Empty             = "Empty"
  showPrec p (Single a)        = prettyShow p $ "Single " ++ showApp a
  showPrec p (Deep _ d1 st d2) = prettyShow p $
    "Deep " ++ showApp d1 ++ " " ++ assert_total (showApp st) ++ " " ++ showApp d2

public export
implementation Sized a => Eq a => Eq (FingerTree a) where
  x == y = case (viewLTree x, viewLTree y) of
    (Just (x1, xs), Just (y1, ys)) => if x1 == y1 
      then assert_total (xs == ys)
      else False
    (Nothing, Nothing) => True
    _                  => False

public export
implementation Sized a => Ord a => Ord (FingerTree a) where
  compare x y = case (viewLTree x, viewLTree y) of
    (Just (x1, xs), Just (y1, ys)) => 
      let res = compare x1 y1
      in if res == EQ
        then assert_total (compare xs ys)
        else res
    (Nothing, Nothing) => EQ
    (_      , Nothing) => GT
    (Nothing, _      ) => LT


-- Zipping
export
zipWith' : (a -> b -> c) -> FingerTree (Elem a) -> FingerTree (Elem b) -> FingerTree (Elem c)
zipWith' f x y = case (viewLTree x, viewLTree y) of
  (Just (x1, xs), Just (y1, ys)) => [|f x1 y1|] `consTree` assert_total (zipWith' f xs ys)
  _ => Empty

export
zipWith3' : (a -> b -> c -> d) -> FingerTree (Elem a) -> FingerTree (Elem b) -> FingerTree (Elem c) -> FingerTree (Elem d)
zipWith3' f x y z = case (viewLTree x, viewLTree y, viewLTree z) of
  (Just (x1, xs), Just (y1, ys), Just (z1, zs)) => [|f x1 y1 z1|] `consTree` assert_total (zipWith3' f xs ys zs)
  _ => Empty

export
unzipWith' : (a -> (b, c)) -> FingerTree (Elem a) -> (FingerTree (Elem b), FingerTree (Elem c))
unzipWith' f zs = foldr app (Empty, Empty) zs
  where
    app : Elem a -> (FingerTree (Elem b), FingerTree (Elem c)) -> (FingerTree (Elem b), FingerTree (Elem c))
    app (MkElem z) (xs, ys) = let (x, y) = f z in (MkElem x `consTree` xs, MkElem y `consTree` ys)

export
unzipWith3' : (a -> (b, c, d)) -> FingerTree (Elem a) 
            -> (FingerTree (Elem b), FingerTree (Elem c), FingerTree (Elem d)) 
unzipWith3' f ws = foldr app (Empty, Empty, Empty) ws
  where
    app : Elem a -> (FingerTree (Elem b), FingerTree (Elem c), FingerTree (Elem d)) 
        -> (FingerTree (Elem b), FingerTree (Elem c), FingerTree (Elem d))
    app (MkElem w) (xs, ys, zs) = 
      let (x, y, z) = f w 
      in (MkElem x `consTree` xs, MkElem y `consTree` ys, MkElem z `consTree` zs)
