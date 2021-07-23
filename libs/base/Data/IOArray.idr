module Data.IOArray

import Data.IOArray.Prims
import Data.List

%default total

export
record IOArray elem where
  constructor MkIOArray
  maxSize : Int
  content : ArrayData elem

export
max : IOArray elem -> Int
max = maxSize

export
newArray : HasIO io => Int -> elem -> io (IOArray elem)
newArray size init
    = pure (MkIOArray size !(primIO (prim__newArray size init)))

export
writeArray : HasIO io => IOArray elem -> Int -> elem -> io Bool
writeArray arr pos el
    = if pos < 0 || pos >= max arr
         then pure False
         else do primIO (prim__arraySet (content arr) pos el)
                 pure True

export
readArray : HasIO io => IOArray elem -> Int -> io (Maybe elem)
readArray arr pos
    = if pos < 0 || pos >= max arr
         then pure Nothing
         else pure $ Just !(primIO (prim__arrayGet (content arr) pos))

-- Make a new array of the given size with the elements copied from the
-- other array
export
newArrayCopy : HasIO io =>
               (newsize : Int) -> (init : elem) -> IOArray elem -> io (IOArray elem)
newArrayCopy newsize init arr
    = do let newsize' = if newsize < max arr then max arr else newsize
         arr' <- newArray newsize' init
         copyFrom (content arr) (content arr') (max arr - 1)
         pure arr'
  where
    copyFrom : ArrayData elem ->
               ArrayData elem ->
               Int -> io ()
    copyFrom old new pos
        = if pos < 0
             then pure ()
             else do el <- primIO $ prim__arrayGet old pos
                     primIO $ prim__arraySet new pos el
                     copyFrom old new $ assert_smaller pos (pos - 1)

export
toList : HasIO io => IOArray elem -> io (List elem)
toList arr = iter 0 (max arr) []
  where
    iter : Int -> Int -> List elem -> io (List elem)
    iter pos end acc
         = if pos >= end
              then pure (reverse acc)
              else do Just el <- readArray arr pos
                        | Nothing => assert_total $ idris_crash "unreachable"
                      assert_total (iter (pos + 1) end (el :: acc))

-- TODO: init is no longer needed when
-- https://github.com/idris-lang/Idris2/pull/1726 merged
export
fromList : HasIO io => elem -> List elem -> io (IOArray elem)
fromList init ns
    = do arr <- newArray (cast (length ns)) init
         addToArray 0 ns arr
         pure arr
  where
    addToArray : Int -> List elem -> IOArray elem -> io ()
    addToArray loc [] arr = pure ()
    addToArray loc (el :: ns) arr
        = do primIO $ prim__arraySet (content arr) loc el
             addToArray (loc + 1) ns arr
