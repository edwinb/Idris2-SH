||| Version of Maybe indexed by an `isJust' boolean
module Data.IMaybe

%default total

public export
data IMaybe : Bool -> Type -> Type where
  Just : a -> IMaybe True a
  Nothing : IMaybe False a

public export
fromJust : IMaybe True a -> a
fromJust (Just a) = a

public export
Functor (IMaybe b) where
  map f (Just a) = Just (f a)
  map f Nothing = Nothing

public export
Apply (IMaybe True) where
  Just f <*> Just x = Just (f x)

public export
Applicative (IMaybe True) where
  pure = Just
