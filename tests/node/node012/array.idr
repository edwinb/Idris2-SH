import Data.IOArray

import System

main : IO ()
main
    = do x <- newArray 20 ""
         True <- writeArray x 10 "Hello"
           | False => do putStrLn "should success 1"
                         exitFailure
         True <- writeArray x 11 "World"
           | False => do putStrLn "should success 2"
                         exitFailure

         False <- writeArray x 20 "World"
           | True => do putStrLn "should fail"
                        exitFailure

         printLn !(toList x)

         y <- fromList 0 [1,2,3,4,5]
         printLn !(toList y)
