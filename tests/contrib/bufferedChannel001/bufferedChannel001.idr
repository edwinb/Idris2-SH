-- test that a new BC is empty

import System.Concurrency.BufferedChannel

main : IO ()
main = do bcRef <- makeBufferedChannel {a=Nat}
          (MkDPair bc recv) <- becomeReceiver NonBlocking bcRef
          Nothing <- recv bc
            | (Just _) => putStrLn "ERROR: Received something from the void."
          putStrLn "Success!"

