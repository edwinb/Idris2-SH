module Arr

import System
import Data.IOArray.Prims

main : IO ()
main = do
  array <- primIO $ prim__newUninitArray 23 {a = String}
  primIO $ prim__arraySet array 17 "x"
  "x" <- primIO $ prim__arrayGet array 17
     | x => do putStrLn (show x)
               exitFailure
  putStrLn "good"
