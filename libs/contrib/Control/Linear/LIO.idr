module Control.Linear.LIO

||| Like `Monad`, but the action and continuation must be run exactly once
||| to ensure that the computation is linear.
public export
interface LinearBind io where
  bindL : (1 _ : io a) -> (1 _ : a -> io b) -> io b

export
LinearBind IO where
  bindL = io_bind

||| Required usage on the result value of a computation
public export
data Usage = None | Linear | Unrestricted

-- Not sure about this, it is a horrible hack, but it makes the notation
-- a bit nicer
public export
fromInteger : (x : Integer) -> {auto _ : Either (x = 0) (x = 1)} -> Usage
fromInteger 0 = None
fromInteger 1 = Linear
fromInteger x = Unrestricted

public export
0 ContType : (Type -> Type) -> Usage -> Usage -> Type -> Type -> Type

||| A wrapper which allows operations to state the multiplicity of the value
||| they return. For example, `L IO {use=1} File` is an IO operation which
||| returns a file that must be used exactly once.
-- This is uglier than I'd like. Perhaps multiplicity polymorphism would make
-- it neater, but we don't have that (yet?), and fortunately none of this
-- horror has to be exposed to the user!
export
data L : (io : Type -> Type) ->
         {default Unrestricted use : Usage} ->
         (ty : Type) -> Type where
     [search ty]
     -- Three separate Pures, because we need to distinguish how they are
     -- used, and this is neater than a continuation.
     Pure0 : (0 _ : a) -> L io {use=0} a
     Pure1 : (1 _ : a) -> L io {use=1} a
     PureW : a -> L io a
     -- The action is always run once, and the type makes an assertion about
     -- how often it's safe to use the result.
     Action : (1 _ : io a) -> L io {use} a
     Bind : {u_act : _} ->
            (1 _ : L io {use=u_act} a) ->
            (1 _ : ContType io u_act u_k a b) ->
            L io {use=u_k} b

public export
L0 : (io : Type -> Type) -> (ty : Type) -> Type
L0 io ty = L io {use = 0} ty

public export
L1 : (io : Type -> Type) -> (ty : Type) -> Type
L1 io ty = L io {use = 1} ty

ContType io None u_k a b = (0 _ : a) -> L io {use=u_k} b
ContType io Linear u_k a b = (1 _ : a) -> L io {use=u_k} b
ContType io Unrestricted u_k a b = a -> L io {use=u_k} b

RunCont : Usage -> Type -> Type -> Type
RunCont None t b = (0 _ : t) -> b
RunCont Linear t b = (1 _ : t) -> b
RunCont Unrestricted t b = t -> b

-- The repetition here is annoying, but necessary because we don't have
-- multiplicity polymorphism. We need to look at the usage to know what the
-- concrete type of the continuation is.
runK : {use : _} ->
       LinearBind io =>
       (1 _ : L io {use} a) -> (1 _ : RunCont use a (io b)) -> io b
runK (Pure0 x) k = k x
runK (Pure1 x) k = k x
runK (PureW x) k = k x
runK {use = None} (Action x) k = bindL x $ \x' => k x'
runK {use = Linear} (Action x) k = bindL x $ \x' => k x'
runK {use = Unrestricted} (Action x) k = bindL x $ \x' => k x'
runK (Bind {u_act = None} act next) k = runK act (\x => runK (next x) k)
runK (Bind {u_act = Linear} act next) k = runK act (\x => runK (next x) k)
runK (Bind {u_act = Unrestricted} act next) k = runK act (\x => runK (next x) k)

||| Run a linear program exactly once, with unrestricted return value in the
||| underlying context
export
run : (Applicative io, LinearBind io) =>
      (1 _ : L io a) -> io a
run prog = runK prog pure

export
Functor io => Functor (L io) where
  map fn act = Bind act $ \a' => PureW (fn a')

export
Applicative io => Applicative (L io) where
  pure = PureW
  (<*>) f a
      = f `Bind` \f' =>
        a `Bind` \a' =>
        PureW (f' a')

export
(Applicative m, LinearBind m) => Monad (L m) where
  (>>=) a k = Bind a k

-- prioritise this one for concrete LIO, so we get the most useful
-- linearity annotations.
export %inline
(>>=) : {u_act : _} ->
        LinearBind io =>
        (1 _ : L io {use=u_act} a) ->
        (1 _ : ContType io u_act u_k a b) -> L io {use=u_k} b
(>>=) = Bind

export
delay : {u_act : _} -> (1 _ : L io {use=u_k} b) -> ContType io u_act u_k () b
delay mb = case u_act of
  None => \ _ => mb
  Linear => \ () => mb
  Unrestricted => \ _ => mb

export %inline
(>>) : {u_act : _} ->
        LinearBind io =>
        (1 _ : L io {use=u_act} ()) ->
        (1 _ : L io {use=u_k} b) -> L io {use=u_k} b
ma >> mb = ma >>= delay mb

export %inline
pure0 : (0 x : a) -> L io {use=0} a
pure0 = Pure0

export %inline
pure1 : (1 x : a) -> L io {use=1} a
pure1 = Pure1

export
(LinearBind io, HasLinearIO io) => HasLinearIO (L io) where
  liftIO1 p = Action (liftIO1 p)

public export
LinearIO : (Type -> Type) -> Type
LinearIO io = (LinearBind io, HasLinearIO io)
