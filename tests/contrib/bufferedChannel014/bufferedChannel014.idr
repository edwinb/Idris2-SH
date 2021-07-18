-- test that things arrive in the order buffered

import System.Concurrency.BufferedChannel

main : IO ()
main =
  do bcRef <- makeBufferedChannel
     let val1 = 1
     let val2 = 2
     let val3 = 3
     (MkDPair bc buffer) <- becomeBuffer bcRef
     (MkDPair bc' recv) <- becomeReceiver Blocking bcRef
     buffer Signal bc [val1, val2, val3]
     val1' <- recv bc'
     val2' <- recv bc'
     val3' <- recv bc'
     if val1 /= val1'
        then putStrLn "ERROR: First value changed in transit."
        else if val2 /= val2'
                then putStrLn "ERROR: Second value changed in transit."
                else if val3 /= val3'
                        then putStrLn "ERROR: Third value changed in transit."
                        else putStrLn "Success!"

