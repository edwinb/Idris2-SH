-- test that sendAndBroadcast doesn't block

import System.Concurrency.BufferedChannel

main : IO ()
main = do bcRef <- makeBufferedChannel
          (MkDPair bc send) <- becomeSender bcRef
          send Broadcast bc 3
          putStrLn "Success!"

