-- check peek doesn't remove things

import System.Concurrency.Queue

main : IO ()
main = do q <- makeQueue {a=Nat}
          let val = 3
          enqueue q val
          (Just theVal) <- peek q
            | Nothing => putStrLn "ERROR: Value disappeared from queue."
          (Just theVal') <- peek q
            | Nothing => putStrLn "ERROR: Peek removed the item."
          if (val == theVal) && (val == theVal')
             then putStrLn "Success!"
             else putStrLn "ERROR: Value changed between calls to peek."

