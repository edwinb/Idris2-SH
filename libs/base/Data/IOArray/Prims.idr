module Data.IOArray.Prims

%default total

export
data ArrayData : Type -> Type where [external]

-- 'unsafe' primitive access, backend dependent
-- get and set assume that the bounds have been checked. Behaviour is undefined
-- otherwise.
export %extern prim__newArray       : forall a . Int -> a -> PrimIO (ArrayData a)
partial
export %extern prim__newUninitArray : forall a . Int -> PrimIO (ArrayData a)
export %extern prim__arrayGet       : forall a . ArrayData a -> Int -> PrimIO a
export %extern prim__arraySet       : forall a . ArrayData a -> Int -> a -> PrimIO ()
