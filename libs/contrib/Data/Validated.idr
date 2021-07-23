module Data.Validated

import Data.List1

import Decidable.Equality

%default total

||| `Validated` is like an `Either` but accumulates all errors with semigroup operation.
public export
data Validated e a = Valid a | Invalid e

--- Instances of standard interfaces ---

public export
(Eq e, Eq a) => Eq (Validated e a) where
  Valid x   == Valid y   = x == y
  Invalid e == Invalid f = e == f
  _ == _ = False

export
(Show e, Show a) => Show (Validated e a) where
  showPrec d $ Valid   x = showCon d "Valid" $ showArg x
  showPrec d $ Invalid e = showCon d "Invalid" $ showArg e

public export
Functor (Validated e) where
  map f $ Valid x   = Valid $ f x
  map _ $ Invalid e = Invalid e

public export
Bifunctor Validated where
  bimap _ s $ Valid x   = Valid   $ s x
  bimap f _ $ Invalid e = Invalid $ f e

public export
Bifoldable Validated where
  bifoldr _ g acc (Valid a)   = g a acc
  bifoldr f _ acc (Invalid e) = f e acc

  bifoldl _ g acc (Valid a)   = g acc a
  bifoldl f _ acc (Invalid e) = f acc e

  binull _ = False

public export
Bitraversable Validated where
  bitraverse _ g (Valid a)   = Valid <$> g a
  bitraverse f _ (Invalid e) = Invalid <$> f e

||| Applicative composition preserves invalidity sequentially accumulating all errors.
public export
Semigroup e => Apply (Validated e) where
  Valid f    <*> Valid x    = Valid $ f x
  Invalid e1 <*> Invalid e2 = Invalid $ e1 <+> e2
  Invalid e  <*> Valid _    = Invalid e
  Valid _    <*> Invalid e  = Invalid e

||| Applicative composition preserves invalidity sequentially accumulating all errors.
public export
Semigroup e => Applicative (Validated e) where
  pure = Valid

-- There is no `Monad` implementation because it can't be coherent with the accumulating `Applicative` one.

||| Semigroup operation selects the leftmost valid value.
||| If both sides are invalid, errors are accumulated.
public export
Semigroup e => Semigroup (Validated e a) where
  l@(Valid _) <+> _           = l
  _           <+> r@(Valid _) = r
  Invalid e1  <+> Invalid e2  = Invalid $ e1 <+> e2

public export
Monoid e => Monoid (Validated e a) where
  neutral = Invalid neutral

||| Alt composition preserves validity selecting the leftmost valid value.
||| If both sides are invalid, errors are accumulated.
public export
Semigroup e => Alt (Validated e) where
  l@(Valid _) <|> _           = l
  _           <|> r@(Valid _) = r
  Invalid e1  <|> Invalid e2  = Invalid $ e1 <+> e2

public export
Monoid e => Plus (Validated e) where
  empty = neutral

public export
Monoid e => Alternative (Validated e) where

public export
Foldable (Validated e) where
  foldr op init $ Valid x   = x `op` init
  foldr _  init $ Invalid _ = init

  foldl op init $ Valid x   = init `op` x
  foldl _  init $ Invalid _ = init

  null $ Valid _   = False
  null $ Invalid _ = True

public export
Traversable (Validated e) where
  traverse f $ Valid x   = Valid <$> f x
  traverse _ $ Invalid e = pure $ Invalid e

public export
Uninhabited (Valid x = Invalid e) where
  uninhabited Refl impossible

public export
Uninhabited (Invalid e = Valid x) where
  uninhabited Refl impossible

public export
(DecEq e, DecEq a) => DecEq (Validated e a) where
  decEq (Valid x) (Invalid y) = No uninhabited
  decEq (Invalid x) (Valid y) = No uninhabited
  decEq (Valid x) (Valid y) with (decEq x y)
    decEq (Valid _) (Valid _) | Yes p = rewrite p in Yes Refl
    decEq (Valid _) (Valid _) | No up = No \case Refl => up Refl
  decEq (Invalid x) (Invalid y) with (decEq x y)
    decEq (Invalid _) (Invalid _) | Yes p = rewrite p in Yes Refl
    decEq (Invalid _) (Invalid _) | No up = No \case Refl => up Refl

--- Convenience representations ---

||| Special case of `Validated` with a `List` as an error accumulator.
public export %inline
ValidatedL : Type -> Type -> Type
ValidatedL e a = Validated (List1 e) a

public export %inline
oneInvalid : e -> Applicative f => Validated (f e) a
oneInvalid x = Invalid $ pure x

--- Conversions to and from `Either` ---

public export %inline
fromEither : Either e a -> Validated e a
fromEither $ Right x = Valid x
fromEither $ Left  e = Invalid e

public export %inline
fromEitherL : Either e a -> ValidatedL e a
fromEitherL $ Right x = Valid x
fromEitherL $ Left  e = oneInvalid e

public export %inline
toEither : Validated e a -> Either e a
toEither $ Valid   x = Right x
toEither $ Invalid e = Left e

--- Conversions to and from `Maybe` ---

public export %inline
fromMaybe : Monoid e => Maybe a -> Validated e a
fromMaybe $ Just x  = Valid x
fromMaybe $ Nothing = empty

public export %inline
toMaybe : Validated e a -> Maybe a
toMaybe $ Valid x   = Just x
toMaybe $ Invalid _ = Nothing

--- Property of being valid ---

public export
data IsValid : Validated e a -> Type where
  ItIsValid : IsValid $ Valid x

export
Uninhabited (IsValid $ Invalid e) where
  uninhabited ItIsValid impossible

public export
isItValid : (v : Validated e a) -> Dec (IsValid v)
isItValid $ Valid _   = Yes ItIsValid
isItValid $ Invalid _ = No absurd
