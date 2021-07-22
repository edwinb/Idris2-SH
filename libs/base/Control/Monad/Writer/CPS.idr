||| Note: The difference to a 'strict' Writer implementation is
||| that accumulation of values does not happen in the
||| Applicative and Monad instances but when invoking `Writer`-specific
||| functions like `writer` or `listen`.
module Control.Monad.Writer.CPS

import Control.Monad.Identity
import Control.Monad.Trans

%default total

||| A writer monad parameterized by:
|||
|||   @w the output to accumulate.
|||
|||   @m The inner monad.
|||
||| The `pure` function produces the output `neutral`, while `>>=`
||| combines the outputs of the subcomputations using `<+>`.
public export
record WriterT (w : Type) (m : Type -> Type) (a : Type) where
  constructor MkWriterT
  unWriterT : w -> m (a, w)

||| Construct an writer computation from a (result,output) computation.
||| (The inverse of `runWriterT`.)
public export %inline
writerT : (Functor m, Semigroup w) => m (a, w) -> WriterT w m a
writerT f = MkWriterT $ \w => (\(a,w') => (a,w <+> w')) <$> f

||| Unwrap a writer computation.
||| (The inverse of 'writerT'.)
public export %inline
runWriterT : Monoid w => WriterT w m a -> m (a,w)
runWriterT m = unWriterT m neutral

||| Extract the output from a writer computation.
public export %inline
execWriterT : (Functor m, Monoid w) => WriterT w m a -> m w
execWriterT = map snd . runWriterT

||| Map both the return value and output of a computation using
||| the given function.
public export %inline
mapWriterT :  (Functor n, Monoid w, Semigroup w')
           => (m (a, w) -> n (b, w')) -> WriterT w m a -> WriterT w' n b
mapWriterT f m = MkWriterT $ \w =>
                  (\(a,w') => (a,w <+> w')) <$> f (runWriterT m)

--------------------------------------------------------------------------------
--          Writer Functions
--------------------------------------------------------------------------------

||| The `return` function produces the output `neutral`, while `>>=`
||| combines the outputs of the subcomputations using `<+>`.
public export
Writer : Type -> Type -> Type
Writer w = WriterT w Identity

||| Unwrap a writer computation as a (result, output) pair.
public export %inline
runWriter : Monoid w => Writer w a -> (a, w)
runWriter = runIdentity . runWriterT

||| Extract the output from a writer computation.
public export %inline
execWriter : Monoid w => Writer w a -> w
execWriter = runIdentity . execWriterT

||| Map both the return value and output of a computation using
||| the given function.
public export %inline
mapWriter :  (Monoid w, Semigroup w')
          => ((a, w) -> (b, w')) -> Writer w a -> Writer w' b
mapWriter f = mapWriterT $ \(Id p) => Id (f p)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
Functor m => Functor (WriterT w m) where
  map f m = MkWriterT $ \w => (\(a,w') => (f a,w')) <$> unWriterT m w

public export %inline
Monad m => Applicative (WriterT w m) where
  pure a = MkWriterT $ \w => pure (a,w)
  MkWriterT mf <*> MkWriterT mx =
    MkWriterT $ \w => do (f,w1) <- mf w
                         (a,w2) <- mx w1
                         pure (f a,w2)

public export %inline
(Monad m, Alternative m) => Alternative (WriterT w m) where
  empty = MkWriterT $ \_ => empty
  MkWriterT m <|> MkWriterT n = MkWriterT $ \w => m w <|> n w

public export %inline
Monad m => Monad (WriterT w m) where
  m >>= k = MkWriterT $ \w => do (a,w1) <- unWriterT m w
                                 unWriterT (k a) w1

public export %inline
MonadTrans (WriterT w) where
  lift m = MkWriterT $ \w => map (\a => (a,w)) m

public export %inline
HasIO m => HasIO (WriterT w m) where
  liftIO = lift . liftIO
