module Data.Late

%default total

------------------------------------------------------------------------
-- Type

public export
data Late : Type -> Type where
  Now : a -> Late a
  Later : Inf (Late a) -> Late a

------------------------------------------------------------------------
-- Creating late values

||| Never return
never : Late a
never = Later never

||| Run a small state machine until it reaches a final state and yields a value.
public export
unfold : (seed -> Either seed value) -> seed -> Late value
unfold f s = case f s of
  Left s' => Later (unfold f s')
  Right v => Now v

||| It's easier to define map and (<*>) in terms of bind so let's start
||| by defining it.
public export
bind : Late a -> (a -> Late b) -> Late b
bind (Now v) f = f v
bind (Later d) f = Later (bind d f)

------------------------------------------------------------------------
-- Inspecting late values

||| Check whether we already have a value.
public export
isNow : Late a -> Maybe a
isNow (Now v) = Just v
isNow (Later d) = Nothing

||| Wait for one tick, hoping to get a value.
public export
wait : Late a -> Late a
wait (Later d) = d
wait d = d

||| Wait for a set number of ticks.
public export
engine : Nat -> Late a -> Late a
engine Z = id
engine (S n) = engine n . wait

||| Wait for a set number of ticks, hoping to get a value.
public export
petrol : Nat -> Late a -> Maybe a
petrol n = isNow . engine n

||| Accelerate makes things happen twice as fast.
public export
accelerate : Late a -> Late a
accelerate (Later (Later d)) = Later (accelerate d)
accelerate (Later (Now v)) = Now v
accelerate d = d

------------------------------------------------------------------------
-- Instances

public export
Functor Late where
  map f d = bind d (Now . f)

public export
Apply Late where
  df <*> dx = bind df (\ f => map (f $) dx)

public export
Applicative Late where
  pure = Now

public export
Bind Late where
  (>>=) = bind

public export
Monad Late where
