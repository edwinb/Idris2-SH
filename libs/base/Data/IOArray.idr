module Data.IOArray

import Data.IOArray.Prims
import Data.List

%default total

export
record IOArray elem where
  constructor MkIOArray
  maxSize : Int
  content : ArrayData (Maybe elem)

export
max : IOArray elem -> Int
max = maxSize

export
newArray : HasIO io => Int -> io (IOArray elem)
newArray size
    = pure (MkIOArray size !(primIO (prim__newArray size Nothing)))

-- Create an array with elements uninitialized.
-- Elements must not be read before elements are written.
partial
newArrayUninitUnsafe : HasIO io => Int -> io (IOArray elem)
newArrayUninitUnsafe size
    = pure (MkIOArray size !(primIO (prim__newUninitArray size)))

export
writeArray : HasIO io => IOArray elem -> Int -> elem -> io Bool
writeArray arr pos el
    = if pos < 0 || pos >= max arr
         then pure False
         else do primIO (prim__arraySet (content arr) pos (Just el))
                 pure True

export
readArray : HasIO io => IOArray elem -> Int -> io (Maybe elem)
readArray arr pos
    = if pos < 0 || pos >= max arr
         then pure Nothing
         else primIO (prim__arrayGet (content arr) pos)

-- Make a new array of the given size with the elements copied from the
-- other array
export
newArrayCopy : HasIO io =>
               (newsize : Int) -> IOArray elem -> io (IOArray elem)
newArrayCopy newsize arr
    = do let newsize' = if newsize < max arr then max arr else newsize
         arr' <- newArray newsize'
         copyFrom (content arr) (content arr') (max arr - 1)
         pure arr'
  where
    copyFrom : ArrayData (Maybe elem) ->
               ArrayData (Maybe elem) ->
               Int -> io ()
    copyFrom old new pos
        = if pos < 0
             then pure ()
             else do el <- primIO $ prim__arrayGet old pos
                     primIO $ prim__arraySet new pos el
                     copyFrom old new $ assert_smaller pos (pos - 1)

export
toList : HasIO io => IOArray elem -> io (List (Maybe elem))
toList arr = iter 0 (max arr) []
  where
    iter : Int -> Int -> List (Maybe elem) -> io (List (Maybe elem))
    iter pos end acc
         = if pos >= end
              then pure (reverse acc)
              else do el <- readArray arr pos
                      assert_total (iter (pos + 1) end (el :: acc))

export
fromList : HasIO io => List (Maybe elem) -> io (IOArray elem)
fromList ns
    = assert_total $ do arr <- newArrayUninitUnsafe (cast (length ns))
                        addToArray 0 ns arr
                        pure arr
  where
    addToArray : Int -> List (Maybe elem) -> IOArray elem -> io ()
    addToArray loc [] arr = pure ()
    addToArray loc (Nothing :: ns) arr = addToArray (loc + 1) ns arr
    addToArray loc (Just el :: ns) arr
        = do primIO $ prim__arraySet (content arr) loc (Just el)
             addToArray (loc + 1) ns arr
