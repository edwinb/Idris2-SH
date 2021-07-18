-- test that await works correctly with buffered signal

import System
import System.Concurrency.BufferedChannel

main : IO ()
main = do bcRef <- makeBufferedChannel
          let val = 3
          (MkDPair bc recv) <- becomeReceiver Blocking bcRef
          child <- fork $ do (MkDPair bc' buffer) <- becomeBuffer bcRef
                             sleep 1    -- give parent time to call recv.
                             buffer Signal bc' [val, val + 1]
          val' <- recv bc
          if val /= val'
             then putStrLn "ERROR: Value changed in transit."
             else do threadWait child
                     putStrLn "Success!"

