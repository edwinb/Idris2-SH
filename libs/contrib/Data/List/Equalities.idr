module Data.List.Equalities

import Data.List

%default total

||| A list constructued using snoc cannot be empty.
export
snocNonEmpty : {x : a} -> {xs : List a} -> Not (xs ++ [x] = [])
snocNonEmpty {xs = []} prf = uninhabited prf
snocNonEmpty {xs = y :: ys} prf = uninhabited prf

||| Proof that snoc'ed list is not empty in terms of `NonEmpty`.
export %hint
SnocNonEmpty : (xs : List a) -> (x : a) -> NonEmpty (xs `snoc` x)
SnocNonEmpty []     _ = IsNonEmpty
SnocNonEmpty (_::_) _ = IsNonEmpty

||| Two lists are equal, if their heads are equal and their tails are equal.
export
consCong2 : {x : a} -> {xs : List a} -> {y : b} -> {ys : List b} ->
            x = y -> xs = ys -> x :: xs = y :: ys
consCong2 Refl Refl = Refl

||| Equal non-empty lists should result in equal components after destructuring 'snoc'.
export
snocInjective : {x : a} -> {xs : List a} -> {y : a} -> {ys : List a} ->
            (xs `snoc` x) = (ys `snoc` y) -> (xs = ys, x = y)
snocInjective {xs = []} {ys = []} Refl = (Refl, Refl)
snocInjective {xs = []} {ys = z :: zs} prf =
  let nilIsSnoc = snd $ consInjective {xs = []} {ys = zs ++ [y]} prf
   in void $ snocNonEmpty (sym nilIsSnoc)
snocInjective {xs = z :: xs} {ys = []} prf =
  let snocIsNil = snd $ consInjective {x = z} {xs = xs ++ [x]} {ys = []} prf
   in void $ snocNonEmpty snocIsNil
snocInjective {xs = w :: xs} {ys = z :: ys} prf =
  let (wEqualsZ, xsSnocXEqualsYsSnocY) = consInjective prf
      (xsEqualsYS, xEqualsY) = snocInjective xsSnocXEqualsYsSnocY
   in (consCong2 wEqualsZ xsEqualsYS, xEqualsY)

||| Appending pairwise equal lists gives equal lists
export
appendCong2 : {x1 : List a} -> {x2 : List a} ->
              {y1 : List b} -> {y2 : List b} ->
              x1 = y1 -> x2 = y2 -> x1 ++ x2 = y1 ++ y2
appendCong2 {x1=[]} {y1=(_ :: _)} Refl _ impossible
appendCong2 {x1=(_ :: _)} {y1=[]} Refl _ impossible
appendCong2 {x1=[]} {y1=[]} _ eq2 = eq2
appendCong2 {x1=(_ :: _)} {y1=(_ :: _)} eq1 eq2 =
  let (hdEqual, tlEqual) = consInjective eq1
   in consCong2 hdEqual (appendCong2 tlEqual eq2)

||| List.map is distributive over appending.
export
mapDistributesOverAppend
  : (f : a -> b)
  -> (xs : List a)
  -> (ys : List a)
  -> map f (xs ++ ys) = map f xs ++ map f ys
mapDistributesOverAppend _ [] _ = Refl
mapDistributesOverAppend f (x :: xs) ys =
  cong (f x ::) $ mapDistributesOverAppend f xs ys

||| List.length is distributive over appending.
export
lengthDistributesOverAppend
  : (xs, ys : List a)
  -> length (xs ++ ys) = length xs + length ys
lengthDistributesOverAppend [] ys = Refl
lengthDistributesOverAppend (x :: xs) ys =
  cong S $ lengthDistributesOverAppend xs ys

||| Length of a snoc'd list is the same as Succ of length list.
export
lengthSnoc : (x : _) -> (xs : List a) -> length (snoc xs x) = S (length xs)
lengthSnoc x [] = Refl
lengthSnoc x (_ :: xs) = cong S (lengthSnoc x xs)

||| Appending the same list at left is injective.
export
appendSameLeftInjective : (xs, ys, zs : List a) -> zs ++ xs = zs ++ ys -> xs = ys
appendSameLeftInjective xs ys []      = id
appendSameLeftInjective xs ys (_::zs) = appendSameLeftInjective xs ys zs . snd . consInjective

||| Appending the same list at right is injective.
export
appendSameRightInjective : (xs, ys, zs : List a) -> xs ++ zs = ys ++ zs -> xs = ys
appendSameRightInjective xs ys [] = rewrite appendNilRightNeutral xs in
                                    rewrite appendNilRightNeutral ys in
                                    id
appendSameRightInjective xs ys (z::zs) = rewrite appendAssociative xs [z] zs in
                                         rewrite appendAssociative ys [z] zs in
                                         fst . snocInjective . appendSameRightInjective (xs ++ [z]) (ys ++ [z]) zs

||| List cannot be equal to itself prepended with some non-empty list.
export
appendNonEmptyLeftNotEq : (zs, xs : List a) -> NonEmpty xs => Not (zs = xs ++ zs)
appendNonEmptyLeftNotEq []      (_::_)  Refl impossible
appendNonEmptyLeftNotEq (z::zs) (_::xs) prf
  = appendNonEmptyLeftNotEq zs (xs ++ [z]) @{SnocNonEmpty xs z}
  $ rewrite sym $ appendAssociative xs [z] zs in snd $ consInjective prf

||| List cannot be equal to itself appended with some non-empty list.
export
appendNonEmptyRightNotEq : (zs, xs : List a) -> NonEmpty xs => Not (zs = zs ++ xs)
appendNonEmptyRightNotEq []      (_::_)  Refl impossible
appendNonEmptyRightNotEq (_::zs) (x::xs) prf = appendNonEmptyRightNotEq zs (x::xs) $ snd $ consInjective prf
