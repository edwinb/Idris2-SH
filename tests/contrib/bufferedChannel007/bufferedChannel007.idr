-- test that await works correctly with broadcast

import System
import System.Concurrency.BufferedChannel

main : IO ()
main = do bcRef <- makeBufferedChannel
          let val = 3
          (MkDPair bc recv) <- becomeReceiver Blocking bcRef
          child <- fork $ do (MkDPair bc' send) <- becomeSender bcRef
                             sleep 1
                             send Broadcast bc' val
          val' <- recv bc
          if val /= val'
             then putStrLn "ERROR: Value changed in transit."
             else do threadWait child
                     putStrLn "Success!"

