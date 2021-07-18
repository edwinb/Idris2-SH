-- dequeue should get the same thing back

import System.Concurrency.Queue

main : IO ()
main = do q <- makeQueue {a=Nat}
          let val = 3
          enqueue q val
          (Just n) <- dequeue q
            | Nothing => putStrLn "ERROR: Value disappeared from queue."
          if n == val
             then putStrLn "Success!"
             else putStrLn "ERROR: Value changed between en- and de-queue."

