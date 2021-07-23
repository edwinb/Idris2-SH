||| There are different flavours of induction-recursion. This is the one
||| introduced in Dybjer and Setzer's paper:
||| Indexed induction-recursion

module Data.InductionRecursion.DybjerSetzer

%default total

public export
data Code : (input : sort -> Type) -> (output : Type) -> Type where
  Yield  : output -> Code input output
  Store  : (payload : Type) -> (payload -> Code input output) -> Code input output
  Branch : (label : Type) -> (toSort : label -> sort) ->
           (((l : label) -> input (toSort l)) -> Code input output) ->
           Code input output

public export
DecodeType
  : Code input output -> (x : sort -> Type) ->
    (f : {s : sort} -> x s -> input s) ->
    Type
DecodeType (Yield _) x f = ()
DecodeType (Store payload k) x f = (v : payload ** DecodeType (k v) x f)
DecodeType (Branch label toSort k) x f
  = (r : ((l : label) -> x (toSort l)) ** DecodeType (k (\ l => f (r l))) x f)

public export
DecodeOutput
  : (c : Code input output) -> (x : Lazy (sort -> Type)) ->
    (f : {s : sort} -> x s -> input s) ->
    DecodeType c x f -> output
DecodeOutput (Yield o) x f _ = o
DecodeOutput (Store p k) x f (v ** d) = DecodeOutput (k v) x f d
DecodeOutput (Branch l s k) x f (r ** d) = DecodeOutput (k (\ l => f (r l))) x f d

mutual

  public export
  data Mu : (f : (s : sort) -> Code input (input s)) -> (s : sort) -> Type where
    MkMu : {f : (s : sort) -> Code input (input s)} -> {s : sort} ->
           DecodeType (f s) (Mu f) Decode -> Mu {input} f s

  public export
  Decode : {f : (s : sort) -> Code input (input s)} ->
           {s : sort} -> Mu {input} f s -> input s
  Decode (MkMu d) = DecodeOutput (f s) (Mu f) (\ d => assert_total (Decode d)) d

public export
bind : Code i o -> (o -> Code i o') -> Code i o'
bind (Yield v) f = f v
bind (Store p k) f = Store p (\ v => bind (k v) f)
bind (Branch l s k) f = Branch l s (\ r => bind (k r) f)

public export
Functor (Code i) where
  map f v = bind v (Yield . f)

public export
Apply (Code i) where
  cf <*> co = bind cf (\ f => map (f $) co)

public export
Applicative (Code i) where
  pure = Yield

public export
Bind (Code i) where
  (>>=) = bind

public export
Monad (Code i) where
