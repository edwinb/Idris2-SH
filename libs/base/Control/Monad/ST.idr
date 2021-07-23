module Control.Monad.ST

import Data.IORef

%default total

export
data STRef : Type -> Type -> Type where
     MkSTRef : IORef a -> STRef s a

export
data ST : Type -> Type -> Type where
     MkST : IO a -> ST s a

export
runST : (forall s . ST s a) -> a
runST p
    = let MkST prog = p {s = ()} in -- anything will do :)
          unsafePerformIO prog

export
Functor (ST s) where
  map fn (MkST st) = MkST $ fn <$> st

export
Apply (ST s) where
  MkST f <*> MkST a = MkST $ f <*> a

export
Applicative (ST s) where
  pure = MkST . pure

export
Bind (ST s) where
  MkST p >>= k
      = MkST $ do p' <- p
                  let MkST kp = k p'
                  kp

export
Monad (ST s) where

export
newSTRef : a -> ST s (STRef s a)
newSTRef val
    = MkST $ do r <- newIORef val
                pure (MkSTRef r)

%inline
export
readSTRef : STRef s a -> ST s a
readSTRef (MkSTRef r) = MkST $ readIORef r

%inline
export
writeSTRef : STRef s a -> (val : a) -> ST s ()
writeSTRef (MkSTRef r) val = MkST $ writeIORef r val

export
modifySTRef : STRef s a -> (a -> a) -> ST s ()
modifySTRef ref f
    = do val <- readSTRef ref
         writeSTRef ref (f val)
