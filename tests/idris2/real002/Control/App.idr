module Control.App

import Data.IORef

public export
Error : Type
Error = Type

public export
Environment : Type
Environment = List Error

public export
data HasErr : Error -> List Error -> Type where
     Here : HasErr e (e :: es)
     There : HasErr e es -> HasErr e (e' :: es)

public export
data Path : Type where
     [noHints]
     MayThrow : Path
     NoThrow : Path

%hint public export
dpath : Path
dpath = MayThrow

public export
data Usage : Type where
     [noHints]
     One : Usage
     Any : Usage

%hint public export
dusage : Usage
dusage = One

public export
0 Has : List (a -> Type) -> a -> Type
Has [] es = ()
Has [e] es = e es
Has (e :: es') es = (e es, Has es' es)

public export
0 excTy : List Error -> List Type
excTy [] = []
excTy (e :: es) = e :: excTy es

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
execTy p es ty = Either (OneOf (excTy es) p) ty

data AppRes : Type -> Type where
     MkAppRes : (result : a) -> (1 x : %World) -> AppRes a

data App1Res : Usage -> Type -> Type where
     MkApp1Res1 : (1 result : a) -> (1 x : %World) -> App1Res One a
     MkApp1ResW : (result : a) -> (1 x : %World) -> App1Res Any a

PrimApp : Type -> Type
PrimApp a = (1 x : %World) -> AppRes a

prim_app_pure : a -> PrimApp a
prim_app_pure x = \w => MkAppRes x w

prim_app_bind : (1 act : PrimApp a) -> (1 k : a -> PrimApp b) -> PrimApp b
prim_app_bind fn k w
    = let MkAppRes x' w' = fn w in k x' w'

toPrimApp : IO a -> PrimApp a
toPrimApp x
    = \w => case toPrim x w of
                 MkIORes r w => MkAppRes r w

PrimApp1 : Usage -> Type -> Type
PrimApp1 u a = (1 x : %World) -> App1Res u a

toPrimApp1 : {u : _} -> IO a -> PrimApp1 u a
toPrimApp1 x
    = \w => case toPrim x w of
                 MkIORes r w =>
                     case u of
                          One => MkApp1Res1 r w
                          Any => MkApp1ResW r w

export
data App : (l : Path) => (e : Environment) -> Type -> Type where
     MkApp : (1 prog : (1 w : %World) -> AppRes (execTy l e t)) -> App {l} e t

export
data App1 : (u : Usage) => (e : Environment) -> Type -> Type where
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

absurdWith1 : (1 w : b) -> OneOf e NoThrow -> any
absurdWith1 w (First p) impossible

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
seqL : App {l=NoThrow} e () -> (1 k : App {l} e b) -> App {l} e b
seqL ma mb = bindL ma (\ () => mb)

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
pureApp x = MkApp $ \w => MkAppRes (Right x) w

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

  export
  delay : {u : _} -> (1 k : App1 {u=u'} e b) ->
          Cont1Type u () u' e b
  delay {u = One} mb = \ () => mb
  delay {u = Any} mb = \ _ => mb

  export
  (>>) : {u : _} -> (1 act : App1 {u} e ()) ->
          (1 k : App1 {u=u'} e b) -> App1 {u=u'} e b
  ma >> mb = ma >>= delay mb

  export
  pure : (x : a) -> App1 {u=Any} e a
  pure x =  MkApp1 $ \w => MkApp1ResW x w

  export
  pure1 : (1 x : a) -> App1 e a
  pure1 x =  MkApp1 $ \w => MkApp1Res1 x w

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
put : (0 tag : _) -> State tag t e => t -> App {l} e ()
put tag @{MkState r} val
    = MkApp $
          prim_app_bind (toPrimApp $ writeIORef r val) $ \val =>
          MkAppRes (Right ())

export
modify : (0 tag : _) -> State tag t e => (t -> t) -> App {l} e ()
modify tag f
    = do x <- get tag
         put tag (f x)

export
new : t -> (State tag t e => App {l} e a) -> App {l} e a
new val prog
    = MkApp $
         prim_app_bind (toPrimApp $ newIORef val) $ \ref =>
            let st = MkState ref
                MkApp res = prog @{st} in
                res

public export
interface Exception err e where
  throw : err -> App e a
  catch : App e a -> (err -> App e a) -> App e a

findException : HasErr e es -> e -> OneOf (excTy es) MayThrow
findException Here err = First err
findException (There p) err = Later $ findException p err

findError : HasErr e es -> OneOf (excTy es) MayThrow -> Maybe e
findError Here (First err) = Just err
findError (There p) (Later q) = findError p q
findError _ _ = Nothing

export
HasErr e es => Exception e es where
  throw err = MkApp $ MkAppRes (Left (findException %search err))
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
Init = [Void]

export
run : App {l} Init a -> IO a
run (MkApp prog)
    = primIO $ \w =>
           case (prim_app_bind prog $ \r =>
                   case r of
                        Right res => MkAppRes res
                        Left (First err) => absurd err) w of
                MkAppRes r w => MkIORes r w

public export
interface PrimIO e where
  primIO : IO a -> App {l} e a
  -- fork starts a new environment, so that any existing state can't get
  -- passed to it (since it'll be tagged with the wrong environment)
  fork : (forall e' . PrimIO e' => App {l} e' ()) -> App e ()

export
HasErr Void e => PrimIO e where
  primIO op =
        MkApp $ \w =>
            let MkAppRes r w = toPrimApp op w in
                MkAppRes (Right r) w
  fork thread
      = MkApp $
            prim_app_bind
                (toPrimApp $ Prelude.fork $
                      do run thread
                         pure ())
                    $ \_ =>
               MkAppRes (Right ())

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
