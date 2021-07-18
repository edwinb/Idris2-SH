-- test that a sent thing arrives and is the thing that was sent

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
          if val /= val'
             then putStrLn "ERROR: Value changed in transit."
             else putStrLn "Success!"

