module System.Future

%default total

-- Futures based Concurrency and Parallelism

export
data Future : Type -> Type where [external]

%extern prim__makeFuture : {0 a : Type} -> Lazy a -> Future a

%foreign "scheme:blodwen-await-future"
prim__awaitFuture : {0 a : Type} -> Future a -> a

export
fork : Lazy a -> Future a
fork = prim__makeFuture

export
await : Future a -> a
await f = prim__awaitFuture f

public export
Functor Future where
  map func future = fork $ func (await future)

public export
Apply Future where
  funcF <*> v = fork $ (await funcF) (await v)

public export
Applicative Future where
  pure v = fork v

public export
Bind Future where
  join = map await
  v >>= func = join . fork $ func (await v)

public export
Monad Future where

export
performFutureIO : HasIO io => Future (IO a) -> io (Future a)
performFutureIO = primIO . prim__io_pure . map unsafePerformIO

export
forkIO : HasIO io => IO a -> io (Future a)
forkIO a = performFutureIO $ fork a
