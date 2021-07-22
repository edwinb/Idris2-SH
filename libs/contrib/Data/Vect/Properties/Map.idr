||| Properties of Data.Vect.map
module Data.Vect.Properties.Map

import Data.Vect.Properties.Tabulate
import Data.Vect.Properties.Index
import Data.Vect.Properties.Foldr

import Data.Vect
import Data.Vect.Elem
import Data.Fin
import Data.Vect.Extra

import Syntax.PreorderReasoning

||| `map` functoriality: identity preservation
export
mapId : (xs : Vect n a) -> map Prelude.id xs = xs
mapId xs = vectorExtensionality _ _ $ \i => indexNaturality _ _ _

||| `mapWtihPos f` represents post-composition the tabulated function `f`
export
indexMapWithPos : (f : Fin n -> a -> b) -> (xs : Vect n a) -> (i : Fin n)
  -> index i (mapWithPos f xs) = f i (index i xs)
indexMapWithPos f (x :: _ )  FZ    = Refl
indexMapWithPos f (_ :: xs) (FS i) = indexMapWithPos _ _ _

||| `tabulate : (Fin n ->) -> Vect n` is a natural transformation
export
mapTabulate : (f : a -> b) -> (g : Fin n -> a)
  -> tabulate (f . g) = map f (tabulate g)
mapTabulate f g = irrelevantEq $
  vectorExtensionality _ _ $ \i => Calc $
  |~ index i (tabulate (f . g))
  ~~ f (g i)                      ...(indexTabulate _ _)
  ~~ f (index i $ tabulate g)     ...(cong f (sym $ indexTabulate _ _))
  ~~ index i (map f $ tabulate g) ...(sym $ indexNaturality _ _ _)

||| Tabulating with the constant function is replication
export
tabulateConstantly : (x : a) -> Fin.tabulate {len} (const x) === replicate len  x
tabulateConstantly x = irrelevantEq $
  vectorExtensionality _ _ $ \i => Calc $
  |~ index i (Fin.tabulate (const x))
  ~~ x ...(indexTabulate _ _)
  ~~ index i (replicate _ x) ...(sym $ indexReplicate _ _)

||| It's enough that two functions agree on the elements of a vector for the maps to agree
export
mapRestrictedExtensional : (f, g : a -> b) -> (xs : Vect n a)
  -> (prf : (i : Fin n) -> f (index i xs) = g (index i xs))
  -> map f xs = map g xs
mapRestrictedExtensional f g xs prf = vectorExtensionality _ _ $ \i => Calc $
  |~ index i (map f xs)
  ~~ f (index i xs)     ...(      indexNaturality _ _ _)
  ~~ g (index i xs)     ...(prf _)
  ~~ index i (map g xs) ...(sym $ indexNaturality _ _ _)

||| function extensionality is a congruence wrt map
export
mapExtensional : (f, g : a -> b)
  -> (prf : (x : a) -> f x = g x)
  -> (xs : Vect n a)
  -> map f xs = map g xs
mapExtensional f g prf xs = mapRestrictedExtensional f g xs (\i => prf (index i xs))

||| map-fusion property for vectors up to function extensionality
export
mapFusion : (f : b -> c) -> (g : a -> b) -> (xs : Vect n a)
  -> map f (map g xs) = map (f . g) xs
mapFusion f g    []     = Refl
mapFusion f g (x :: xs) = cong (f $ g x ::) $ mapFusion f g xs

||| function extensionality is a congruence wrt mapWithElem
export
mapWithElemExtensional : (xs : Vect n a) -> (f, g :  (x : a) -> (0 _ : x `Elem` xs) -> b)
  -> ((x : a) -> (0 pos : x `Elem` xs) -> f x pos = g x pos)
  -> mapWithElem xs f = mapWithElem xs g
mapWithElemExtensional    []     f g prf = Refl
mapWithElemExtensional (x :: xs) f g prf
  = cong2 (::) (prf x Here)
               (mapWithElemExtensional xs _ _ (\x,pos => prf x (There pos)))
