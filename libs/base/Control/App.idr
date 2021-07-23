module Control.App

import Data.IORef

%default covering

||| `Error` is a type synonym for `Type`, specify for exception handling.
public export
Error : Type
Error = Type

public export
data HasErr : Error -> List Error -> Type where
     Here : HasErr e (e :: es)
     There : HasErr e es -> HasErr e (e' :: es)

||| States whether the program's execution path is linear or might throw exceptions so that we can know
||| whether it is safe to reference linear resources.
public export
data Path = MayThrow | NoThrow

public export
data Usage = One | Any

public export
0 Has : List (a -> Type) -> a -> Type
Has [] es = ()
Has [e] es = e es
Has (e :: es') es = (e es, Has es' es)

data OneOf : List Type -> Path -> Type where
     First : e -> OneOf (e :: es) MayThrow
     Later : OneOf es MayThrow -> OneOf (e :: es) MayThrow

public export
data SafeBind : Path -> (l' : Path) -> Type where
     [search l']
     SafeSame : SafeBind l l
     SafeToThrow : SafeBind NoThrow MayThrow

updateP : SafeBind p p' => OneOf es p -> OneOf es p'
updateP @{SafeSame} x = x
updateP @{SafeToThrow} x impossible

Uninhabited (OneOf [] p) where
  uninhabited (First x) impossible
  uninhabited (Later x) impossible

Uninhabited (OneOf es NoThrow) where
  uninhabited (First x) impossible
  uninhabited (Later x) impossible

0 execTy : Path -> List Error -> Type -> Type
execTy p es ty = Either (OneOf es p) ty

data AppRes : Type -> Type where
     MkAppRes : (result : a) -> (1 x : %World) -> AppRes a

data App1Res : Usage -> Type -> Type where
     MkApp1Res1 : (1 result : a) -> (1 x : %World) -> App1Res One a
     MkApp1ResW : (result : a) -> (1 x : %World) -> App1Res Any a

PrimApp : Type -> Type
PrimApp a = (1 x : %World) -> AppRes a

prim_app_pure : a -> PrimApp a
prim_app_pure = MkAppRes

prim_app_bind : (1 act : PrimApp a) -> (1 k : a -> PrimApp b) -> PrimApp b
prim_app_bind fn k w
    = let MkAppRes x' w' = fn w in k x' w'

toPrimApp : (1 act : IO a) -> PrimApp a
toPrimApp x
    = \w => case toPrim x w of
                 MkIORes r w => MkAppRes r w

PrimApp1 : Usage -> Type -> Type
PrimApp1 u a = (1 x : %World) -> App1Res u a

toPrimApp1 : {u : _} -> (1 act : IO a) -> PrimApp1 u a
toPrimApp1 x
    = \w => case toPrim x w of
                 MkIORes r w =>
                     case u of
                          One => MkApp1Res1 r w
                          Any => MkApp1ResW r w

prim_app1_bind : (1 act : PrimApp1 Any a) ->
                 (1 k : a -> PrimApp1 u b) -> PrimApp1 u b
prim_app1_bind fn k w
    = let MkApp1ResW x' w' = fn w in k x' w'

||| A type supports throwing and catching exceptions. See `interface Exception err e` for details.
||| @ l  An implicit Path states whether the program's execution path is linear or might throw
|||      exceptions. The default value is `MayThrow` which represents that the program might throw.
||| @ es A list of exception types that can be thrown. Constrained interfaces can be defined by
|||      parameterising with a list of errors `es`.
export
data App : {default MayThrow l : Path} ->
           (es : List Error) -> Type -> Type where
     MkApp : (1 prog : (1 w : %World) -> AppRes (execTy l e t)) -> App {l} e t

export
data App1 : {default One u : Usage} ->
            (es : List Error) -> Type -> Type where
     MkApp1 : (1 prog : (1 w : %World) -> App1Res u t) -> App1 {u} e t

bindApp : SafeBind l l' =>
          App {l} e a -> (a -> App {l=l'} e b) -> App {l=l'} e b
bindApp (MkApp prog) next
    = MkApp $ \world =>
          let MkAppRes x' world' = prog world in
              case x' of
                   Right res =>
                         let MkApp r = next res in
                             r world'
                   Left err => MkAppRes (Left (updateP err)) world'

public export
Cont1Type : Usage -> Type -> Usage -> List Error -> Type -> Type
Cont1Type One a u e b = (1 x : a) -> App1 {u} e b
Cont1Type Any a u e b = (x : a) -> App1 {u} e b

export
bindApp1 : {u : _} -> (1 act : App1 {u} e a) ->
           (1 k : Cont1Type u a u' e b) -> App1 {u=u'} e b
bindApp1 {u=One} (MkApp1 fn)
    = \k => MkApp1 (\w => let MkApp1Res1 x' w' = fn w
                              MkApp1 res = k x' in
                              res w')
bindApp1 {u=Any} (MkApp1 fn)
    = \k => MkApp1 (\w => let MkApp1ResW x' w' = fn w
                              MkApp1 res = k x' in
                              res w')

||| When type is present in app "errors" list, app is allowed to perform I/O.
public export
data AppHasIO : Type where

public export
Uninhabited AppHasIO where
  uninhabited _ impossible

absurdWith1 : (1 w : b) -> OneOf e NoThrow -> any
absurdWith1 w (First p) impossible

absurdWithAppHasIO : (1 w : b) -> OneOf [AppHasIO] t -> any
absurdWithAppHasIO w (First p) impossible

absurdWith2 : (1 x : a) -> (1 w : b) -> OneOf e NoThrow -> any
absurdWith2 x w (First p) impossible

export
bindL : App {l=NoThrow} e a -> (1 k : a -> App {l} e b) -> App {l} e b
bindL (MkApp prog) next
    = MkApp $ \world =>
          let MkAppRes x' world' = prog world in
              case x' of
                   Right res =>
                         let MkApp r = next res in
                             r world'
                   Left err => absurdWith2 next world' err

export
app : (1 p : App {l=NoThrow} e a) -> App1 {u=Any} e a
app (MkApp prog)
    = MkApp1 $ \world =>
          let MkAppRes x' world' = prog world in
              case x' of
                   Left err => absurdWith1 world' err
                   Right res => MkApp1ResW res world'

export
app1 : (1 p : App1 {u=Any} e a) -> App {l} e a
app1 (MkApp1 prog)
    = MkApp $ \world =>
          let MkApp1ResW x' world' = prog world in
              MkAppRes (Right x') world'

pureApp : a -> App {l} e a
pureApp x = MkApp $ MkAppRes (Right x)

export
Functor (App {l} es) where
  map f ap = bindApp ap $ \ap' => pureApp (f ap')

export
Apply (App {l} es) where
  (<*>) f a = bindApp f $ \f' =>
              bindApp a $ \a' => pureApp (f' a')

export
Applicative (App {l} es) where
  pure = pureApp

export
Bind (App es) where
  (>>=) = bindApp -- won't get used, but handy to have the instance

export
Monad (App es) where

export
(>>=) : SafeBind l l' =>
        App {l} e a -> (k : a -> App {l=l'} e b) -> App {l=l'} e b
(>>=) = bindApp

namespace App1
  export
  (>>=) : {u : _} -> (1 act : App1 {u} e a) ->
          (1 k : Cont1Type u a u' e b) -> App1 {u=u'} e b
  (>>=) = bindApp1

  delay : {u_act : _} -> (1 _ : App1 {u=u_k} e b) -> Cont1Type u_act () u_k e b
  delay mb = case u_act of
                  One => \ () => mb
                  Any => \ _ => mb

  export %inline
  (>>) : {u_act : _} -> (1 _ : App1 {u=u_act} e ()) ->
         (1 _ : App1 {u=u_k} e b) -> App1 {u=u_k} e b
  ma >> mb = ma >>= delay mb

  export
  pure : (x : a) -> App1 {u=Any} e a
  pure x =  MkApp1 $ MkApp1ResW x

  export
  pure1 : (1 x : a) -> App1 e a
  pure1 x =  MkApp1 $ MkApp1Res1 x

export
data State : (tag : a) -> Type -> List Error -> Type where
     [search tag]
     MkState : IORef t -> State tag t e

%hint export
mapState : State tag t e -> State tag t (eff :: e)
mapState (MkState s) = MkState s

export
get : (0 tag : _) -> State tag t e => App {l} e t
get tag @{MkState r}
    = MkApp $
          prim_app_bind (toPrimApp $ readIORef r) $ \val =>
          MkAppRes (Right val)

export
put : (0 tag : _) -> State tag t e => (val : t) -> App {l} e ()
put tag @{MkState r} val
    = MkApp $
          prim_app_bind (toPrimApp $ writeIORef r val) $ \val =>
          MkAppRes (Right ())

export
modify : (0 tag : _) -> State tag t e => (p : t -> t) -> App {l} e ()
modify tag f
    = let (>>=) = bindL in
          do x <- get tag
             put tag (f x)

export
new : t -> (p : State tag t e => App {l} e a) -> App {l} e a
new val prog
    = MkApp $
         prim_app_bind (toPrimApp $ newIORef val) $ \ref =>
            let st = MkState ref
                MkApp res = prog @{st} in
                res

||| An alias for `HasErr`.
public export
Exception : Error -> List Error -> Type
Exception = HasErr

findException : HasErr e es -> e -> OneOf es MayThrow
findException Here err = First err
findException (There p) err = Later $ findException p err

findError : HasErr e es -> OneOf es MayThrow -> Maybe e
findError Here (First err) = Just err
findError (There p) (Later q) = findError p q
findError _ _ = Nothing

export
throw : HasErr err es => err -> App es a
throw err = MkApp $ MkAppRes (Left (findException %search err))

export
catch : HasErr err es => App es a -> (err -> App es a) -> App es a
catch (MkApp prog) handler
      = MkApp $
           prim_app_bind prog $ \res =>
              case res of
                   Left err =>
                        case findError %search err of
                             Nothing => MkAppRes (Left err)
                             Just err' =>
                                  let MkApp e' = handler err' in
                                      e'
                   Right ok => MkAppRes (Right ok)

export
handle : App (err :: e) a ->
         (onok : a -> App e b) ->
         (onerr : err -> App e b) -> App e b
handle (MkApp prog) onok onerr
    = MkApp $
           prim_app_bind prog $ \res =>
             case res of
                  Left (First err) =>
                        let MkApp err' = onerr err in
                            err'
                  Left (Later p) =>
                        -- different exception, so rethrow
                        MkAppRes (Left p)
                  Right ok =>
                        let MkApp ok' = onok ok in
                            ok'

export
lift : App e a -> App (err :: e) a
lift (MkApp prog)
    = MkApp $
           prim_app_bind prog $ \res =>
            case res of
                 Left err => MkAppRes (Left (Later err))
                 Right ok => MkAppRes (Right ok)

public export
Init : List Error
Init = [AppHasIO]

||| The only way provided by `Control.App` to run an App.
||| @ Init A concrete list of errors.
export
run : App {l} Init a -> IO a
run (MkApp prog)
    = primIO $ \w =>
           case (prim_app_bind prog $ \r =>
                   case r of
                        Right res => MkAppRes res
                        Left (First err) => absurd err) w of
                MkAppRes r w => MkIORes r w

export
noThrow : App Init a -> App Init {l=NoThrow} a
noThrow (MkApp prog)
    = MkApp $ \w =>
              case prog w of
                   MkAppRes (Left err) w => absurdWithAppHasIO w err
                   MkAppRes (Right res) w => MkAppRes (Right res) w

public export
interface PrimIO e where
  primIO : IO a -> App {l} e a
  primIO1 : (1 act : IO a) -> App1 e a
  -- fork starts a new environment, so that any existing state can't get
  -- passed to it (since it'll be tagged with the wrong environment)
  fork : (forall e' . PrimIO e' => App {l} e' ()) -> App e ()

export
HasErr AppHasIO e => PrimIO e where
  primIO op =
        MkApp $ \w =>
            let MkAppRes r w = toPrimApp op w in
                MkAppRes (Right r) w

  primIO1 op = MkApp1 $ toPrimApp1 op

  fork thread
      = MkApp $
            prim_app_bind
                (toPrimApp $ Prelude.fork $
                      do run thread
                         pure ())
                    $ \_ =>
               MkAppRes (Right ())

export
new1 :  t -> (1 p : State tag t e => App1 {u} e a) -> App1 {u} e a
new1 val prog
    = MkApp1 $ prim_app1_bind (toPrimApp1 $ newIORef val) $ \ref =>
        let st = MkState ref
            MkApp1 res = prog @{st} in
            res

public export
data FileEx = GenericFileEx Int -- errno
            | FileReadError
            | FileWriteError
            | FileNotFound
            | PermissionDenied
            | FileExists

export
Show FileEx where
  show (GenericFileEx errno) = "File error: " ++ show errno
  show FileReadError = "File Read Error"
  show FileWriteError = "File Write Error"
  show FileNotFound = "File Not Found"
  show PermissionDenied = "Permission Denied"
  show FileExists = "File Exists"

public export
data IOError
     = GenericErr String
     | FileErr FileEx

export
Show IOError where
  show (GenericErr str) = "IO error: " ++ str
  show (FileErr f) = "File error: " ++ show f
