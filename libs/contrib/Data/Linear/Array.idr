module Data.Linear.Array

import Data.IOArray

-- Linear arrays. General idea: mutable arrays are constructed linearly,
-- using newArray. Once everything is set up, they can be converted to
-- read only arrays with constant time, pure, access, using toIArray.

-- Immutable arrays which can be read in constant time, but not updated
public export
interface Array arr where
  read : (1 _ : arr t) -> Int -> Maybe t
  size : (1 _ : arr t) -> Int

-- Mutable arrays which can be used linearly
public export
interface Array arr => MArray arr where
  newArray : (size : Int) -> t -> (1 _ : (1 _ : arr t) -> a) -> a
  -- Array is unchanged if the index is out of bounds
  write : (1 _ : arr t) -> Int -> t -> Res Bool (const (arr t))

  mread : (1 _ : arr t) -> Int -> Res (Maybe t) (const (arr t))
  msize : (1 _ : arr t) -> Res Int (const (arr t))

export
data IArray : Type -> Type where
     MkIArray : IOArray t -> IArray t

export
data LinArray : Type -> Type where
     MkLinArray : IOArray t -> LinArray t

-- Convert a mutable array to an immutable array
export
toIArray : (1 _ : LinArray t) -> (IArray t -> a) -> a
toIArray (MkLinArray arr) k = k (MkIArray arr)

export
Array LinArray where
  read (MkLinArray a) i = unsafePerformIO (readArray a i)
  size (MkLinArray a) = max a

export
MArray LinArray where
  newArray size init k = k (MkLinArray (unsafePerformIO (newArray size init)))

  write (MkLinArray a) i el
      = unsafePerformIO (do ok <- writeArray a i el
                            pure (ok # MkLinArray a))
  msize (MkLinArray a) = max a # MkLinArray a
  mread (MkLinArray a) i
      = unsafePerformIO (readArray a i) # MkLinArray a

export
Array IArray where
  read (MkIArray a) i = unsafePerformIO (readArray a i)
  size (MkIArray a) = max a

export
copyArray : MArray arr => (newsize : Int) -> (init : t) -> (1 _ : arr t) ->
            LPair (arr t) (arr t)
copyArray newsize init a
    = let size # a = msize a in
          newArray newsize init $
            copyContent (min (newsize - 1) (size - 1)) a
  where
    copyContent : Int -> (1 _ : arr t) -> (1 _ : arr t) -> LPair (arr t) (arr t)
    copyContent pos a a'
        = if pos < 0
             then a # a'
             else let val # a = mread a pos
                      1 a' = case val of
                                  Nothing => a'
                                  Just v => let (ok # a') = write a' pos v in
                                            a' in
                      copyContent (pos - 1) a a'
