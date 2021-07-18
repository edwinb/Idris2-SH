-- test that bufferAndBroadcast doesn't block

import System.Concurrency.BufferedChannel

main : IO ()
main = do bcRef <- makeBufferedChannel
          (MkDPair bc buffer) <- becomeBuffer bcRef
          buffer Broadcast bc [1,2,3]
          putStrLn "Success!"

