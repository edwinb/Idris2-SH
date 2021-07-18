||| A channel built on top of System.Concurrency.Queue. It is MTSafe thanks to
||| Queues being MTSafe, and buffered as it operates using a Queue of things.
module System.Concurrency.BufferedChannel

import public Data.List
import System.Concurrency

import public System.Concurrency.Queue

%default total

||| A channel for inter-process communication where one side is the sender, and
||| the other is the receiver.
||| See also:
||| - @makeBufferedChannel@
||| - @becomeSender@
||| - @becomeReceiver@
export
data BufferedChannel : Type -> Type where
  MkBufferedChannel : (condLock : Mutex)
                    -> (condVar : Condition)
                    -> (qRef    : IORef (Queue a))
                    -> BufferedChannel a

||| Create a new BufferedChannel. Since BufferedChannels are shared resources,
||| they can only be obtained in an IORef.
||| See also
||| - @becomeSender@
||| - @becomeReceiver@
export
makeBufferedChannel : IO (IORef (BufferedChannel a))
makeBufferedChannel =
  do cl <- makeMutex
     cv <- makeCondition
     q  <- makeQueue
     newIORef (MkBufferedChannel cl cv q)


-- Sending --

||| The type of a sender function is something which takes a channel and a thing
||| to send, and produces an empty IO action, i.e. the sending of the thing.
public export
SenderFunc : Type -> Type
SenderFunc a = BufferedChannel a -> a -> IO ()

||| What sending should do to the BufferedChannel's internal Condition Variable:
||| - Signalling wakes 1 thread waiting to receive, if there are any.
||| - Broadcasting wakes all the threads waiting to receive, if there are any.
public export
data SendEffect = Signal
                | Broadcast

||| Send a thing on the BufferedChannel and signal its internal condition
||| variable.
|||
||| MTSafe: YES
sendAndSignal : SenderFunc a
sendAndSignal (MkBufferedChannel _ condVar qRef) thing =
  do enqueue qRef thing
     conditionSignal condVar

||| Send a thing on the BufferedChannel and broadcast its internal condition
||| variable.
|||
||| MTSafe: YES
sendAndBroadcast : SenderFunc a
sendAndBroadcast (MkBufferedChannel _ condVar qRef) thing =
  do enqueue qRef thing
     conditionBroadcast condVar

||| Send a thing on the BC, affecting the internal CV in the specified way.
send : SendEffect -> SenderFunc a
send Signal = sendAndSignal
send Broadcast = sendAndBroadcast

||| The type of a buffer function is something which takes a channel and
||| non-empty list of things to send, and produces an empty IO action, i.e. the
||| sending of the things.
public export
BufferFunc : Type -> Type
BufferFunc a =
  BufferedChannel a -> (items : List a) -> {auto 0 ok : NonEmpty items} -> IO ()

||| Send some things in bulk on the BufferedChannel and signal its internal
||| condition variable.
bufferAndSignal : BufferFunc a
bufferAndSignal (MkBufferedChannel _ condVar qRef) things =
  do ignore $ traverse (\thing => enqueue qRef thing) things
     conditionSignal condVar

||| Send some things in bulk on the BufferedChannel and broadcast its internal
||| condition variable.
bufferAndBroadcast : BufferFunc a
bufferAndBroadcast (MkBufferedChannel _ condVar qRef) things =
  do ignore $ traverse (\thing => enqueue qRef thing) things
     conditionBroadcast condVar

||| Buffer a list of things on the BC, affecting the internal CV in the
||| specified way.
buffer : SendEffect -> BufferFunc a
buffer Signal = bufferAndSignal
buffer Broadcast = bufferAndBroadcast

-- Obtaining send access --

||| Given a reference to a BufferedChannel obtain the channel and the ability to
||| send on the channel given the desired effect sending should have on any
||| potentially waiting receiver-threads.
export
becomeSender : (bcRef : IORef (BufferedChannel a))
             -> IO (dc : BufferedChannel a ** (SendEffect -> SenderFunc a))
becomeSender bcRef =
  do bc <- readIORef bcRef
     pure (MkDPair bc send)

||| Given a reference to a BufferedChannel obtain the channel and the ability to
||| buffer a list of items on the channel given the desired effect sending
||| should have on any potentially waiting receiver-threads.
export
becomeBuffer : (bcRef : IORef (BufferedChannel a))
             -> IO (dc : BufferedChannel a ** (SendEffect -> BufferFunc a))
becomeBuffer bcRef =
  do bc <- readIORef bcRef
     pure (MkDPair bc buffer)

-- Receiving --

||| The type of a receiver function which takes a channel and produces an IO
||| action containing the next thing on the channel if there is one, and Nothing
||| otherwise.
public export
NonBlockingReceiver : Type -> Type
NonBlockingReceiver a = BufferedChannel a -> IO (Maybe a)

||| The type of a receiver function which takes a channel and produces an
||| IO action which is guaranteed to contain the next thing on the channel.
public export
BlockingReceiver : Type -> Type
BlockingReceiver a = BufferedChannel a -> IO a

||| Crash Idris with a message signalling that something went wrong in terms of
||| the fundamental guarantees of condition variables.
|||
||| Essentially, the point of waiting on a CV is to wait until something is
||| available for consumption. So as soon as the CV lets us past, there will be
||| something to retrieve. However, Idris doesn't know this.
await_crash : IO a
await_crash =
  assert_total $ idris_crash "Await somehow got Nothing despite waiting on a CV"

||| Try to receive a thing on the channel without blocking until something
||| appears.
|||
||| MTSafe: YES
receive : NonBlockingReceiver a
receive (MkBufferedChannel condLock condVar qRef) = dequeue qRef

||| Try to receive the next thing and if there is Nothing, block on the
||| BufferedChannel's internal condition variable until something arrives, and
||| at that point, retrieve that thing.
|||
||| MTSafe: YES
await : BlockingReceiver a
await (MkBufferedChannel condLock condVar qRef) =
  do (Just thing) <- dequeue qRef
          -- if there wasn't anything in the queue, wait until something appears
        | Nothing => do mutexAcquire condLock
                        conditionWait condVar condLock
                        (Just thing') <- dequeue qRef
                           | Nothing => await_crash
                        mutexRelease condLock
                        pure thing'
     pure thing

-- Obtaining receive access --

||| How receiving on a channel should behave:
||| - A non-blocking receiver is not guaranteed to always get a thing when it
|||   receives, but never blocks the receiving thread.
||| - A blocking receiver is guaranteed to always get a thing when it receives,
|||   but may block the receiving thread until something arrives.
public export
data ReceiveType = NonBlocking
                 | Blocking

||| Given a reference to a BufferedChannel and a choice between weather the
||| receive operation should block the thread until something arrives or not,
||| obtain the channel and the ability to receive on it in the desired manner.
export
becomeReceiver : (1 recvType : ReceiveType)
               -> (bcRef : IORef (BufferedChannel a))
               -> case recvType of
                       NonBlocking => IO (dc : BufferedChannel a
                                               ** (NonBlockingReceiver a))
                       Blocking => IO (dc : BufferedChannel a
                                            ** (BlockingReceiver a))
becomeReceiver NonBlocking bcRef = do bc <- readIORef bcRef
                                      pure (MkDPair bc receive)
becomeReceiver Blocking bcRef = do bc <- readIORef bcRef
                                   pure (MkDPair bc await)

