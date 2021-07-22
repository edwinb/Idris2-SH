module Control.Monad.Writer.Interface

import Control.Monad.Maybe
import Control.Monad.Error.Either
import Control.Monad.Reader.Reader
import Control.Monad.State.State
import Control.Monad.RWS.CPS
import Control.Monad.Trans
import Control.Monad.Writer.CPS

%default total

||| MonadWriter interface
|||
||| tell is like tell on the MUD's it shouts to monad
||| what you want to be heard. The monad carries this 'packet'
||| upwards, merging it if needed (hence the Monoid requirement).
|||
||| listen listens to a monad acting, and returns what the monad "said".
|||
||| pass lets you provide a writer transformer which changes internals of
||| the written object.
public export
interface (Monoid w, Monad m) => MonadWriter w m | m where
  ||| `writer (a,w)` embeds a simple writer action.
  writer : (a,w) -> m a
  writer (a, w) = tell w $> a

  ||| `tell w` is an action that produces the output `w`.
  tell : w -> m ()
  tell w = writer ((),w)

  ||| `listen m` is an action that executes the action `m` and adds
  ||| its output to the value of the computation.
  listen : m a -> m (a, w)

  ||| `pass m` is an action that executes the action `m`, which
  ||| returns a value and a function, and returns the value, applying
  ||| the function to the output.
  pass : m (a, w -> w) -> m a

||| `listens f m` is an action that executes the action `m` and adds
||| the result of applying @f@ to the output to the value of the computation.
public export
listens : MonadWriter w m => (w -> b) -> m a -> m (a, b)
listens f = map (\(a,w) => (a,f w)) . listen

||| `censor f m` is an action that executes the action `m` and
||| applies the function `f` to its output, leaving the return value
||| unchanged.
public export
censor : MonadWriter w m => (w -> w) -> m a -> m a
censor f = pass . map (\a => (a,f))

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
(Monoid w, Monad m) => MonadWriter w (WriterT w m) where
  writer   = writerT . pure

  listen m = MkWriterT $ \w =>
               (\(a,w') => ((a,w'),w <+> w')) <$> runWriterT m

  tell w'  = writer ((), w')

  pass m   = MkWriterT $ \w =>
               (\((a,f),w') => (a,w <+> f w')) <$> runWriterT m

public export %inline
(Monoid w, Monad m) => MonadWriter w (RWST r w s m) where
  writer (a,w') = MkRWST $ \_,s,w => pure (a,s,w <+> w')

  tell w' = writer ((), w')

  listen m = MkRWST $ \r,s,w =>
               (\(a,s',w') => ((a,w'),s',w <+> w')) <$> runRWST m r s

  pass m = MkRWST $ \r,s,w =>
             (\((a,f),s',w') => (a,s',w <+> f w')) <$> runRWST m r s

public export %inline
MonadWriter w m => MonadWriter w (EitherT e m) where
  writer = lift . writer
  tell   = lift . tell
  listen = mapEitherT $ \m => do (e,w) <- listen m
                                 pure $ map (\a => (a,w)) e

  pass   = mapEitherT $ \m => pass $ do Right (r,f) <- m
                                          | Left l => pure $ (Left l, id)
                                        pure (Right r, f)

public export %inline
MonadWriter w m => MonadWriter w (MaybeT m) where
  writer = lift . writer
  tell   = lift . tell
  listen = mapMaybeT $ \m => do (e,w) <- listen m
                                pure $ map (\a => (a,w)) e

  pass   = mapMaybeT $ \m => pass $ do Just (r,f) <- m
                                         | Nothing => pure $ (Nothing, id)
                                       pure (Just r, f)
public export %inline
MonadWriter w m => MonadWriter w (ReaderT r m) where
  writer = lift . writer
  tell   = lift . tell
  listen = mapReaderT listen
  pass   = mapReaderT pass

public export %inline
MonadWriter w m => MonadWriter w (StateT s m) where
  writer = lift . writer
  tell   = lift . tell
  listen (ST m) = ST $ \s => do ((s',a),w) <- listen (m s)
                                pure (s',(a,w))

  pass   (ST m) = ST $ \s => pass $ do (s',(a,f)) <- m s
                                       pure ((s',a),f)
