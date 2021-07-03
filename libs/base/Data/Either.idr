module Data.Either

import public Control.Function
import Data.List1

%default total

--------------------------------------------------------------------------------
-- Checking for a specific constructor

||| Extract the Left value, if possible
public export
getLeft : Either a b -> Maybe a
getLeft (Left a) = Just a
getLeft _ = Nothing

||| Extract the Right value, if possible
public export
getRight : Either a b -> Maybe b
getRight (Right b) = Just b
getRight _ = Nothing

||| True if the argument is Left, False otherwise
public export
isLeft : Either a b -> Bool
isLeft (Left _)  = True
isLeft (Right _) = False

||| True if the argument is Right, False otherwise
public export
isRight : Either a b -> Bool
isRight (Left _)  = False
isRight (Right _) = True

--------------------------------------------------------------------------------
-- Grouping values

mutual

  ||| Compress the list of Lefts and Rights by accumulating
  ||| all of the lefts and rights into non-empty blocks.
  export
  compress : List (Either a b) -> List (Either (List1 a) (List1 b))
  compress [] = []
  compress (Left a :: abs) = compressLefts (singleton a) abs
  compress (Right b :: abs) = compressRights (singleton b) abs

  compressLefts : List1 a -> List (Either a b) -> List (Either (List1 a) (List1 b))
  compressLefts acc (Left a :: abs) = compressLefts (cons a acc) abs
  compressLefts acc abs = Left (reverse acc) :: compress abs

  compressRights : List1 b -> List (Either a b) -> List (Either (List1 a) (List1 b))
  compressRights acc (Right b :: abs) = compressRights (cons b acc) abs
  compressRights acc abs = Right (reverse acc) :: compress abs

||| Decompress a compressed list. This is the left inverse of `compress` but not its
||| right inverse because nothing forces the input to be maximally compressed!
export
decompress : List (Either (List1 a) (List1 b)) -> List (Either a b)
decompress = concatMap $ \ abs => case abs of
  Left as => map Left  $ forget as
  Right bs => map Right $ forget bs

||| Keep the payloads of all Left constructors in a list of Eithers
public export
lefts : List (Either a b) -> List a
lefts []              = []
lefts (Left  l :: xs) = l :: lefts xs
lefts (Right _ :: xs) = lefts xs

||| Keep the payloads of all Right constructors in a list of Eithers
public export
rights : List (Either a b) -> List b
rights []              = []
rights (Left  _ :: xs) = rights xs
rights (Right r :: xs) = r :: rights xs

||| Split a list of Eithers into a list of the left elements and a list of the right elements
public export
partitionEithers : List (Either a b) -> (List a, List b)
partitionEithers l = (lefts l, rights l)

||| Remove a "useless" Either by collapsing the case distinction
public export
fromEither : Either a a -> a
fromEither (Left l)  = l
fromEither (Right r) = r

||| Right becomes left and left becomes right
public export
mirror : Either a b -> Either b a
mirror (Left  x) = Right x
mirror (Right x) = Left x

--------------------------------------------------------------------------------
-- Bifunctor

export
pushInto : c -> Either a b -> Either (c, a) (c, b)
pushInto c = bimap (\ a => (c, a)) (\ b => (c, b))
  -- ^ not using sections to keep it backwards compatible

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

||| Convert a Maybe to an Either by using a default value in case of Nothing
||| @ e the default value
public export
maybeToEither : (def : Lazy e) -> Maybe a -> Either e a
maybeToEither def (Just j) = Right j
maybeToEither def Nothing  = Left  def

||| Convert an Either to a Maybe from Right injection
public export
eitherToMaybe : Either e a -> Maybe a
eitherToMaybe (Left _) = Nothing
eitherToMaybe (Right x) = Just x

-- Injectivity of constructors

||| Left is injective
export
Injective Left where
  injective Refl = Refl

||| Right is injective
export
Injective Right where
  injective Refl = Refl
