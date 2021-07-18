-- new queue should be empty

import System.Concurrency.Queue

main : IO ()
main = do q <- makeQueue {a=Nat}
          Nothing <- dequeue q
            | (Just x) => putStrLn "ERROR: New queue contained something."
          putStrLn "Success!"

