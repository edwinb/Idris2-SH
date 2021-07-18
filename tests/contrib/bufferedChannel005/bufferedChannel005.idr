-- test that a sent thing arrives and is the thing that was sent

import System
import System.Concurrency.BufferedChannel

main : IO ()
main = do bcRef <- makeBufferedChannel
          let val = 3
          (MkDPair bc send) <- becomeSender bcRef
          (MkDPair bc' recv) <- becomeReceiver Blocking bcRef

          send Signal bc val
          val' <- recv bc'
          if val /= val'
             then putStrLn "ERROR: Value changed in transit."
             else putStrLn "Success!"

