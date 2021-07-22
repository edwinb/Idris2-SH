module Control.Monad.Reader.Interface

import Control.Monad.Maybe
import Control.Monad.Error.Either
import Control.Monad.Reader.Reader
import Control.Monad.State.State
import Control.Monad.RWS.CPS
import Control.Monad.Trans
import Control.Monad.Writer.CPS

%default total

||| A computation which runs in a static context and produces an output
public export
interface Monad m => MonadReader stateType m | m where
  ||| Get the context
  ask : m stateType

  ||| `local f c` runs the computation `c` in an environment modified by `f`.
  local : (stateType -> stateType) -> m a -> m a


||| Evaluate a function in the context held by this computation
public export
asks : MonadReader stateType m => (stateType -> a) -> m a
asks f = map f ask

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
Monad m => MonadReader stateType (ReaderT stateType m) where
  ask = MkReaderT (\st => pure st)

  local f (MkReaderT action) = MkReaderT (action . f)

public export %inline
Monad m => MonadReader r (RWST r w s m) where
  ask       = MkRWST $ \r,s,w => pure (r,s,w)
  local f m = MkRWST $ \r,s,w => unRWST m (f r) s w

public export %inline
MonadReader r m => MonadReader r (EitherT e m) where
  ask = lift ask
  local = mapEitherT . local

public export %inline
MonadReader r m => MonadReader r (MaybeT m) where
  ask = lift ask
  local = mapMaybeT . local

public export %inline
MonadReader r m => MonadReader r (StateT s m) where
  ask = lift ask
  local = mapStateT . local

public export %inline
MonadReader r m => MonadReader r (WriterT w m) where
  ask   = lift ask

  -- this differs from the implementation in the mtl package
  -- which uses mapWriterT. However, it seems strange that
  -- this should require a Monoid instance to further
  -- accumulate values, while the implementation of
  -- MonadReader for RWST does no such thing.
  local f (MkWriterT m) = MkWriterT $ \w => local f (m w)
