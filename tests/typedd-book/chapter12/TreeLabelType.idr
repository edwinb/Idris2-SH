data Tree a = Empty
            | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ val :: flatten right

data State : (stateType : Type) -> Type -> Type where
     Get : State stateType stateType
     Put : stateType -> State stateType ()

     Pure : ty -> State stateType ty
     Bind : State stateType a -> (a -> State stateType b) ->
             State stateType b

{-
(>>=) : State stateType a -> (a -> State stateType b) ->
        State stateType b
(>>=) = Bind
-}

mutual
  Functor (State stateType) where
      map func x = do val <- x
                      Pure (func val)

  Apply (State stateType) where
      (<*>) f a = do func <- f
                     arg <- a
                     pure (func arg)

  Applicative (State stateType) where
      pure x = Pure x

  Bind (State stateType) where
      (>>=) = Bind

  Monad (State stateType) where

runState : State stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put newState) st = ((), newState)

runState (Pure x) st = (x, st)
runState (Bind cmd prog) st = let (val, nextState) = runState cmd st in
                                  runState (prog val) nextState

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = Pure Empty
treeLabelWith (Node left val right)
     = do left_labelled <- treeLabelWith left
          (this :: rest) <- Get
          Put rest
          right_labelled <- treeLabelWith right
          Pure (Node left_labelled (this, val) right_labelled)

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = fst (runState (treeLabelWith tree) [1..])
