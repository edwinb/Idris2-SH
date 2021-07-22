||| The Error monad (also called the Exception monad).
module Control.Monad.Error.Interface

import Control.Monad.Error.Either
import Control.Monad.Maybe
import Control.Monad.RWS.CPS
import Control.Monad.Reader.Reader
import Control.Monad.State.State
import Control.Monad.Trans
import Control.Monad.Writer.CPS

%default total

||| The strategy of combining computations that can throw exceptions
||| by bypassing bound functions
||| from the point an exception is thrown to the point that it is handled.
||| Is parameterized over the type of error information and
||| the monad type constructor.
||| It is common to use `Either String` as the monad type constructor
||| for an error monad in which error descriptions take the form of strings.
||| In that case and many other common cases the resulting monad is already defined
||| as an instance of the 'MonadError' class.
public export
interface Monad m => MonadError e m | m where
  ||| Is used within a monadic computation to begin exception processing.
  throwError : e -> m a

  ||| A handler function to handle previous errors and return to normal execution.
  ||| A common idiom is:
  |||
  ||| ```idris example
  ||| do { action1; action2; action3 } `catchError` handler
  ||| ```
  catchError : m a -> (e -> m a) -> m a

||| Lifts an `Either e` into any `MonadError e`.
public export
liftEither : MonadError e m => Either e a -> m a
liftEither = either throwError pure

||| Makes a success or failure of an action visible in
||| the return type.
public export
tryError : MonadError e m => m a -> m (Either e a)
tryError action = (map Right action) `catchError` (pure . Left)

||| `MonadError` analogue to the `withEitherT` function.
||| Modify the value (but not the type) of an error.
||| If you need to change the type of `e` use `mapError`.
public export
withError : MonadError e m => (e -> e) -> m a -> m a
withError f action = tryError action >>= either (throwError . f) pure

||| Flipped version of `catchError`.
public export
handleError : MonadError e m => (e -> m a) -> m a -> m a
handleError = flip catchError

||| `MonadError` analogue of the `mapEitherT` function.  The
||| computation is unwrapped, a function is applied to the `Either`, and
||| the result is lifted into the second `MonadError` instance.
public export
mapError : (MonadError e m, MonadError e' n)
         => (m (Either e a) -> n (Either e' b)) -> m a -> n b
mapError f action = f (tryError action) >>= liftEither

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
MonadError () Maybe where
  throwError ()        = Nothing
  catchError Nothing f = f ()
  catchError x       _ = x

public export
MonadError e (Either e) where
  throwError             = Left
  Left  l `catchError` h = h l
  Right r `catchError` _ = Right r

public export
Monad m => MonadError e (EitherT e m) where
  throwError = throwE
  catchError = catchE

public export
MonadError e m => MonadError e (MaybeT m) where
  throwError = lift . throwError
  catchError (MkMaybeT m) f = MkMaybeT (catchError m (runMaybeT . f))

public export
MonadError e m => MonadError e (ReaderT r m) where
  throwError = lift . throwError
  catchError (MkReaderT m) f =
    MkReaderT $ \e => catchError (m e) (runReaderT e . f)

public export
MonadError e m => MonadError e (StateT r m) where
  throwError = lift . throwError
  catchError (ST m) f =
    ST $ \s => catchError (m s) (runStateT s . f)

public export
MonadError e m => MonadError e (RWST r w s m) where
  throwError = lift . throwError
  catchError (MkRWST m) f =
    MkRWST $ \r,w,s => catchError (m r w s) (\e => unRWST (f e) r w s)

public export
MonadError e m => MonadError e (WriterT w m) where
  throwError = lift . throwError
  catchError (MkWriterT m) f =
    MkWriterT $ \w => catchError (m w) (\e => unWriterT (f e) w)
