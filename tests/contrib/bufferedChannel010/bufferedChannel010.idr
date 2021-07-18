-- test that bufferAndSignal doesn't block

import System.Concurrency.BufferedChannel

main : IO ()
main = do bcRef <- makeBufferedChannel
          (MkDPair bc buffer) <- becomeBuffer bcRef
          buffer Signal bc [1,2,3]
          putStrLn "Success!"

