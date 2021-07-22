module Control.Monad.State.State

import Control.Monad.Identity
import Control.Monad.Trans

%default total

||| The transformer on which the State monad is based
public export
record StateT (stateType : Type) (m : Type -> Type) (a : Type) where
  constructor ST
  runStateT' : stateType -> m (stateType, a)

||| Unwrap and apply a StateT monad computation.
public export
%inline
runStateT : stateType -> StateT stateType m a -> m (stateType, a)
runStateT s act = runStateT' act s

||| Unwrap and apply a StateT monad computation, but discard the final state.
public export %inline
evalStateT : Functor m => stateType -> StateT stateType m a -> m a
evalStateT s = map snd . runStateT s

||| Unwrap and apply a StateT monad computation, but discard the resulting value.
public export %inline
execStateT : Functor m => stateType -> StateT stateType m a -> m stateType
execStateT s = map fst . runStateT s

||| Map both the return value and final state of a computation using
||| the given function.
public export %inline
mapStateT : (m (s, a) -> n (s, b)) -> StateT s m a -> StateT s n b
mapStateT f m = ST $ f . runStateT' m

--------------------------------------------------------------------------------
--          State
--------------------------------------------------------------------------------

||| The State monad. See the MonadState interface
public export
State : (stateType : Type) -> (ty : Type) -> Type
State = \s, a => StateT s Identity a

||| Unwrap and apply a State monad computation.
public export %inline
runState : stateType -> State stateType a -> (stateType, a)
runState s act = runIdentity (runStateT s act)

||| Unwrap and apply a State monad computation, but discard the final state.
public export %inline
evalState : stateType -> State stateType a -> a
evalState s = snd . runState s

||| Unwrap and apply a State monad computation, but discard the resulting value.
public export %inline
execState : stateType -> State stateType a -> stateType
execState s = fst . runState s

||| Map both the return value and final state of a computation using
||| the given function.
public export %inline
mapState : ((s, a) -> (s, b)) -> State s a -> State s b
mapState f = mapStateT $ \(Id p) => Id (f p)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
implementation Functor f => Functor (StateT stateType f) where
    map f (ST g) = ST (\st => map (map f) (g st)) where

public export
implementation Monad f => Applicative (StateT stateType f) where
    pure x = ST (\st => pure (st, x))

    (ST f) <*> (ST a)
        = ST (\st =>
                do (r, g) <- f st
                   (t, b) <- a r
                   pure (t, g b))

public export
implementation Monad m => Monad (StateT stateType m) where
    (ST f) >>= k
        = ST (\st =>
                do (st', v) <- f st
                   let ST kv = k v
                   kv st')

public export
implementation MonadTrans (StateT stateType) where
    lift x
        = ST (\st =>
                do r <- x
                   pure (st, r))

public export
implementation (Monad f, Alternative f) => Alternative (StateT st f) where
    empty = lift empty
    (ST f) <|> (ST g) = ST (\st => f st <|> g st)

public export
implementation HasIO m => HasIO (StateT stateType m) where
  liftIO io = ST $ \s => liftIO $ io_bind io $ \a => pure (s, a)
