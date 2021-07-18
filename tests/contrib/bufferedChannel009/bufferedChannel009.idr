-- test that receive consumes a thing from the channel

import System
import System.Concurrency.BufferedChannel

main : IO ()
main = do bcRef <- makeBufferedChannel
          let val = 3
          (MkDPair bc send) <- becomeSender bcRef
          (MkDPair bc' recv) <- becomeReceiver NonBlocking bcRef
          send Signal bc val
          sleep 1   -- give the value time to propagate
          (Just val') <- recv bc'
            | Nothing => putStrLn "ERROR: Value disappeared from channel."
          Nothing <- recv bc'
            | (Just _) => putStrLn "ERROR: Sent a single thing but received 2."
          putStrLn "Success!"

