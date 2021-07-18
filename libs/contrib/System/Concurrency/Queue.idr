||| A queue implementation based on the description in "Purely Functional Data
||| Structures" by Chris Okasaki
module System.Concurrency.Queue

import Data.List
import System.Concurrency

import public Data.IORef

-----------
-- Stack --
-----------

||| A convenient alias to make it easier to reason about operations
Stack : Type -> Type
Stack = List

emptyStack : Stack a
emptyStack = []

||| Create a new, empty stack.
||| For internal use.
makeSharedStack : IO (IORef (Stack a))
makeSharedStack = newIORef emptyStack

||| Put something on the top of the stack.
||| For internal use.
|||
||| MTSafe: NO
push : (sRef : IORef (Stack a)) -> (thing : a) -> IO ()
push sRef thing = modifyIORef sRef ((::) thing)

||| Get the first item on the stack if there is one, removing it in the process.
||| For internal use.
|||
||| MTSafe: NO
pop : (sRef : IORef (Stack a)) -> IO (Maybe a)
pop sRef = do stack <- readIORef sRef
              case stack of
                   [] => pure Nothing
                   (x :: xs) => do writeIORef sRef xs
                                   pure (Just x)

||| Get the first item on the stack if there is one, without removing it.
||| For internal use.
|||
||| MTSafe: NO
stackPeek : (sRef : IORef (Stack a)) -> IO (Maybe a)
stackPeek sRef = do stack <- readIORef sRef
                    case stack of
                         [] => pure Nothing
                         (x :: xs) => pure (Just x)

-----------
-- Queue --
-----------

||| A FIFO data structure.
export
data Queue : Type -> Type where
  MkQueue : (front : IORef (Stack a))
          -> (rear : IORef (Stack a))
          -> (lock : Mutex)
          -> Queue a

-- Accessors and constructor function --

||| Accessor for `front`.
||| For internal use.
getFront : Queue a -> IORef (Stack a)
getFront (MkQueue front _ _) = front

||| Accessor for `rear`.
||| For internal use.
getRear : Queue a -> IORef (Stack a)
getRear (MkQueue _ rear _) = rear

||| Create a new, empty queue.
export
makeQueue : IO (IORef (Queue a))
makeQueue =
  do front <- makeSharedStack
     rear <- makeSharedStack
     lock <- makeMutex
     newIORef (MkQueue front rear lock)


-- Lock manipulation --

||| Lock the queue by acquiring its mutex.
||| For internal use.
lockQueue : Queue _ -> IO ()
lockQueue (MkQueue _ _ lock) = mutexAcquire lock

||| Unlock the queue by releasing its mutex.
||| For internal use.
unlockQueue : Queue _ -> IO ()
unlockQueue (MkQueue _ _ lock) = mutexRelease lock


-- Queue manipulation --

||| Move the `rear` to the `front`. Used when the queue appears to have run out
||| of items but there may be items in the rear.
||| For internal use.
|||
||| MTSafe: NO
reorder : (frontRef : IORef (Stack a))
        -> (rearRef : IORef (Stack a))
        -> IO ()
reorder frontRef rearRef =
  do rear <- readIORef rearRef
     case rear of
          [] => pure ()   -- Nothing to do
          xs => do writeIORef frontRef (reverse xs)
                   writeIORef rearRef emptyStack

||| Put a thing at the end of the queue.
|||
||| MTSafe: YES
export
enqueue : (sharedQueue : IORef (Queue a))
        -> (thing : a)
        -> IO ()
enqueue sharedQueue thing =
  do queue <- readIORef sharedQueue
     lockQueue queue
     push (getRear queue) thing
     unlockQueue queue

||| Get a thing from the front of the queue if there is one, removing it in the
||| process.
|||
||| MTSafe: YES
export
dequeue : (sharedQueue : IORef (Queue a))
        -> IO (Maybe a)
dequeue sharedQueue =
  do queue <- readIORef sharedQueue
     lockQueue queue
     let frontRef = getFront queue
     let rearRef  = getRear  queue
     maybeFront <- pop frontRef
     case maybeFront of
          (Just thing) => do unlockQueue queue
                             pure (Just thing)

          Nothing => do -- reorder and try again
                        reorder frontRef rearRef
                        maybeFront' <- pop frontRef
                        -- no need to inspect maybeFront' since theres nothing
                        -- to do if we got another Nothing; then the queue is
                        -- empty
                        unlockQueue queue
                        pure maybeFront'

||| Get a thing from the front of the queue if there is one, without removing
||| it.
|||
||| MTSafe: YES
export
peek : (sharedQueue : IORef (Queue a))
        -> IO (Maybe a)
peek sharedQueue =
  do queue <- readIORef sharedQueue
     lockQueue queue
     let frontRef = getFront queue
     let rearRef  = getRear  queue
     maybeFront <- stackPeek frontRef
     case maybeFront of
          (Just thing) => do unlockQueue queue
                             pure (Just thing)

          Nothing => do -- reorder and try again
                        reorder frontRef rearRef
                        maybeFront' <- stackPeek frontRef
                        -- no need to inspect maybeFront' since theres nothing
                        -- to do if we got another Nothing; then the queue is
                        -- empty
                        unlockQueue queue
                        pure maybeFront'

