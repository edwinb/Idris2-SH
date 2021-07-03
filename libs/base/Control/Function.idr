module Control.Function

public export
interface Injective (f : a -> b) where
  injective : f x = f y -> x = y
