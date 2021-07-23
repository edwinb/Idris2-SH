module Control.Monad.Error.Either

-------------------------------------------------
-- The monad transformer `EitherT e m a` equips a monad with the ability to
-- return a choice of two values.

-- Sequenced actions of `Either e m a` produce a value `a` only if none of the
-- actions in the sequence returned `e`. Because returning `e` exits the
-- computation early, this can be seen as equipping a monad with the ability to
-- throw an exception.

-- This is more powerful than MaybeT which instead equips a monad with the
-- ability to not return a result.
-------------------------------------------------

import Control.Monad.Trans

%default total

public export
data EitherT : (e : Type) -> (m : Type -> Type) -> (a : Type) -> Type where
  MkEitherT : m (Either e a) -> EitherT e m a

public export
%inline
runEitherT : EitherT e m a -> m (Either e a)
runEitherT (MkEitherT x) = x

public export
eitherT : Monad m => (a -> m c) -> (b -> m c) -> EitherT a m b -> m c
eitherT f g x = runEitherT x >>= either f g

||| map the underlying computation
||| The basic 'unwrap, apply, rewrap' of this transformer.
public export
%inline
mapEitherT : (m (Either e a) -> n (Either e' a')) -> EitherT e m a -> EitherT e' n a'
mapEitherT f = MkEitherT . f . runEitherT

public export
bimapEitherT : Functor m => (a -> c) -> (b -> d)
            -> EitherT a m b -> EitherT c m d
bimapEitherT f g x = mapEitherT (map (either (Left . f) (Right . g))) x

||| Analogous to Left, aka throwE
public export
%inline
left : Applicative m => e -> EitherT e m a
left = MkEitherT . pure . Left

||| Analogous to Right, aka pure for EitherT
public export
%inline
right : Applicative m => a -> EitherT e m a
right = MkEitherT . pure . Right

public export
swapEitherT : Functor m => EitherT e m a -> EitherT a m e
swapEitherT = mapEitherT (map (either Right Left))

-------------------------------------------------
-- Methods of the 'exception' theme
-------------------------------------------------

||| aka `left`
public export
%inline
throwE : Applicative m => e -> EitherT e m a
throwE = MkEitherT . pure . Left

public export
catchE : Monad m => EitherT e m a -> (e -> EitherT e' m a) -> EitherT e' m a
catchE et f
  = MkEitherT $ runEitherT et >>= either (runEitherT . f) (pure . Right)


-------------------------------------------------
-- Interface Implementations
-------------------------------------------------

public export
Eq (m (Either e a)) => Eq (EitherT e m a) where
 (==) = (==) `on` runEitherT

public export
Ord (m (Either e a)) => Ord (EitherT e m a) where
 compare = compare `on` runEitherT

public export
Show (m (Either e a)) => Show (EitherT e m a) where
  showPrec d (MkEitherT x) = showCon d "MkEitherT" $ showArg x

-- I'm not actually confident about having this instance but it is a sane
-- default and since idris has named implementations it can be swapped out at
-- the use site.
public export
Monad m => Semigroup (EitherT e m a) where
  MkEitherT x <+> MkEitherT y = MkEitherT $ do
    r@(Right _) <- x
      | Left _ => y
    pure r

public export
Functor m => Functor (EitherT e m) where
  map f e = MkEitherT $ map f <$> runEitherT e

public export
Foldable m => Foldable (EitherT e m) where
  foldr f acc (MkEitherT e)
    = foldr (\x,xs => either (const xs) (`f` xs) x) acc e

  null (MkEitherT e) = null e

public export
Traversable m => Traversable (EitherT e m) where
  traverse f (MkEitherT x)
    = MkEitherT <$> traverse (either (pure . Left) (map Right . f)) x

public export
Apply m => Apply (EitherT e m) where
  f <*> x = MkEitherT $ (<*>) <$> runEitherT f <*> runEitherT x

public export
Applicative m => Applicative (EitherT e m) where
  pure = MkEitherT . pure . Right

public export
Monad m => Bind (EitherT e m) where
  x >>= k = MkEitherT $ runEitherT x >>= either (pure . Left) (runEitherT . k)

public export
Monad m => Monad (EitherT e m) where

public export
(Monad m, Semigroup e) => Alt (EitherT e m) where
  MkEitherT x <|> MkEitherT y = MkEitherT $ do
    Left l <- x
      | Right r => pure (Right r)
    Left l' <- y
      | Right r => pure (Right r)
    pure (Left (l <+> l'))

||| Plus instance that collects left results, allowing you to try
||| multiple possibilities and combine failures.
public export
(Monad m, Monoid e) => Plus (EitherT e m) where
  empty = left neutral

public export
(Monad m, Monoid e) => Alternative (EitherT e m) where

public export
MonadTrans (EitherT e) where
  lift = MkEitherT . map Right

public export
HasIO m => HasIO (EitherT e m) where
  liftIO act = MkEitherT $ liftIO (io_bind act (pure . Right))
