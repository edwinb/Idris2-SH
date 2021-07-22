module Control.Monad.State.Interface

import Control.Monad.Maybe
import Control.Monad.Error.Either
import Control.Monad.Reader.Reader
import Control.Monad.State.State
import Control.Monad.RWS.CPS
import Control.Monad.Trans
import Control.Monad.Writer.CPS

%default total

||| A computation which runs in a context and produces an output
public export
interface Monad m => MonadState stateType m | m where
    ||| Get the context
    get : m stateType
    ||| Write a new context/output
    put : stateType -> m ()

    ||| Embed a simple state action into the monad.
    state : (stateType -> (stateType,a)) -> m a
    state f = do s <- get
                 let (s2,a) = f s
                 put s2
                 pure a

||| Apply a function to modify the context of this computation
public export
modify : MonadState stateType m => (stateType -> stateType) -> m ()
modify f
    = do s <- get
         put (f s)

||| Evaluate a function in the context held by this computation
public export
gets : MonadState stateType m => (stateType -> a) -> m a
gets f
    = do s <- get
         pure (f s)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
Monad m => MonadState stateType (StateT stateType m) where
    get     = ST (\x => pure (x, x))
    put x   = ST (\y => pure (x, ()))
    state f = ST $ pure . f

public export %inline
MonadState s m => MonadState s (EitherT e m) where
  get = lift get
  put = lift . put
  state = lift . state

public export %inline
MonadState s m => MonadState s (MaybeT m) where
  get = lift get
  put = lift . put
  state = lift . state

public export %inline
Monad m => MonadState s (RWST r w s m) where
  get     = MkRWST $ \_,s,w => pure (s,s,w)
  put s   = MkRWST $ \_,_,w => pure ((),s,w)
  state f = MkRWST $ \_,s,w => let (s',a) = f s in pure (a,s',w)

public export %inline
MonadState s m => MonadState s (ReaderT r m) where
  get = lift get
  put = lift . put
  state = lift . state

public export %inline
MonadState s m => MonadState s (WriterT r m) where
  get = lift get
  put = lift . put
  state = lift . state
