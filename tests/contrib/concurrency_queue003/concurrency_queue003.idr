-- check dequeuing removes things

import System.Concurrency.Queue

main : IO ()
main = do q <- makeQueue {a=Nat}
          enqueue q 3
          (Just theVal) <- dequeue q
            | Nothing => putStrLn "ERROR: Value disappeared from queue."
          Nothing <- dequeue q
            | (Just huh) => putStrLn "ERROR: Dequeue didn't remove the item."
          putStrLn "Success!"

