import Data.Vect

All : (a : i -> j -> Type) -> Type
All a {i} {j} = {x : i} -> {y : j} -> a x y

Matrix : Type -> Nat -> Nat -> Type
Matrix a n m = Vect n (Vect m a)

infixr 1 :->
(:->) : (a, b : i -> j -> Type) -> (i -> j -> Type)
(:->) a b i j = a i j -> b i j

justShowAll : Maybe (All (Matrix Integer :-> Matrix String))
justShowAll = Just (\${x, y} => ?justShowAll_rhs)

justShowAllImpl : Maybe (All (Matrix Integer :-> Matrix String))
justShowAllImpl = Just (\${x, y} => map (map show))
