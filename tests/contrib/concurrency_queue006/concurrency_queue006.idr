-- check that reorder works correctly

import System.Concurrency.Queue

main : IO ()
main =
  do q <- makeQueue
     let val1 = 1
     let val2 = 2
     let val3 = 3
     -- enqueue 2 values, which go on the rear stack
     enqueue q val1
     enqueue q val2
     -- dequeue to reorder
     (Just val1') <- dequeue q
       | Nothing => putStrLn "ERROR: First two values disappeared."
     if val1' == val2
        then putStrLn "ERROR: Queue behaved like a stack (broken reorder)."
        else do enqueue q val3    -- should go on rear; front contains val2
                (Just val2') <- dequeue q
                   | Nothing => putStrLn "ERROR: Second value disappeared."
                if val2' /= val2
                   then putStrLn "ERROR: Second value changed."
                   else do (Just val3') <- dequeue q
                              | Nothing =>
                                    putStrLn "ERROR: Third value disappeared."
                           if (val1 == val1')
                               && (val2 == val2')
                               && (val3 == val3')
                              then putStrLn "Success!"
                              else putStrLn "ERROR: Got different values back."

