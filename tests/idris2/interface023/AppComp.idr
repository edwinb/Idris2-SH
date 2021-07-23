module AppComp

import Control.Monad.Error.Either
import Control.Monad.Identity

-- Errorful monadic functions --

f1 : Monad m => Int -> m (Either String Int)
f1 5 = pure $ Right 0
f1 _ = pure $ Left "fail 1"

f2 : Monad m => Int -> m (Either String Int)
f2 6 = pure $ Right 0
f2 _ = pure $ Left "fail 2"

-- Compositions --

c1 : Monad m => m (Either String Int)
c1 = f1 1 *> f2 1

c2 : Monad m => m (Either String Int)
c2 = (f1 1 *> f2 1) @{Apply.Compose}

c3 : Monad m => m (Either String Int)
c3 = runEitherT $ MkEitherT {m} (f1 1) *> MkEitherT {m} (f2 1)

-- These checks are meant to be true --

r1 : Bool
r1 = runIdentity c1 == Left "fail 2"

r2 : Bool
r2 = runIdentity c2 == Left "fail 1"

r3 : Bool
r3 = runIdentity c3 == Left "fail 1"
