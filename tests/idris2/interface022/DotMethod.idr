data D = MkD
data E = MkE

data Proxy i = MkProxy

interface I i where
 (.idot) : i -> Int

I D where
 (.idot) _ = 0

interface J i where
 theInt  : Proxy i -> Int

 (.jdot) : i -> Int
 (.jdot) _ = theInt (the (Proxy i) MkProxy)

J D where
  theInt _ = 0

J E where
  theInt _ = 0
  (.jdot) _ = 1
