mutual
  data MyBool = MyFalse | MyTrue

  even : Nat -> MyBool
  even (S k) = odd k
  even Z = MyTrue

  odd : Nat -> MyBool
  odd (S k) = even k
  odd Z = MyFalse

eodd : Nat -> (Bool, Bool)
eodd num = (isEven num, isOdd num)
  where
    mutual
      isEven : Nat -> Bool
      isEven (S k) = isOdd k
      isEven Z = True

      isOdd : Nat -> Bool
      isOdd (S k) = isEven k
      isOdd Z = False

data Box : Type -> Type where
     MkBox : a -> Box a

mutual
  Functor Box where
    map f b
        = do b' <- b
             pure (f b')

  Apply Box where
    (<*>) f a
        = do f' <- f
             a' <- a
             pure (f' a')

  Applicative Box where
    pure = MkBox

  Bind Box where
    (>>=) (MkBox val) k = k val

  Monad Box where

boxy : Box Integer
boxy = map (*2) (MkBox 20)
