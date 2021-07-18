-- test that things arrive in the order sent

import System.Concurrency.BufferedChannel

main : IO ()
main = do bcRef <- makeBufferedChannel
          let val1 = 1
          let val2 = 2
          (MkDPair bc send) <- becomeSender bcRef
          (MkDPair bc' recv) <- becomeReceiver Blocking bcRef
          send Signal bc val1
          send Signal bc val2
          val1' <- recv bc'
          val2' <- recv bc'
          if val1 /= val1'
             then putStrLn "ERROR: First value changed in transit."
             else if val2 /= val2'
                     then putStrLn "ERROR: Second value changed in transit."
                     else putStrLn "Success!"

