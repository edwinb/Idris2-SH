%default total

{- -- interfaces don't work yet
{0 a : Type} -> (foo : Show a) => Show (Maybe a) where
-}

showMaybe : {0 a : Type} -> (assumption : Show a) => Maybe a -> String
showMaybe x@ma = case ma of
    Nothing => "Nothing"
    Just a => "Just " ++ show a

doBlock : Maybe Nat
doBlock
  = do let a = 3
       let b = 5
       c <- Just 7
       let (d, e) = (c, c)
       f <- [| Nothing + Just d |]
       pure $ sum [a,b,c,d,e,f]

parameters (x, y, z : Nat)

  add3 : Nat
  add3 = x + y + z

parameters (x, y : Nat) (z, a : Nat)

  add4 : Nat
  add4 = x + y + z + a

anonLam : Maybe (m : Nat ** n : Nat ** m === n)
anonLam = map (\m => (m ** m ** Refl))
        $ map (uncurry $ \ m, n => m + n)
        $ map (\ (m, n) => (n, m))
        $ map (\ m => (m, m))
        $ map (\ m => S m)
        doBlock
