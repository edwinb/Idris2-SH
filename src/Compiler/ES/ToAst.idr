||| Functionality to convert an Idris `NamedCExp`
||| to a sequence of imperative statements.
module Compiler.ES.ToAst

import Data.DPair
import Data.Nat
import Data.List1
import Data.Vect
import Compiler.Common
import Core.CompileExpr
import Core.Context
import Compiler.ES.Ast
import Compiler.ES.State
import Libraries.Data.SortedMap

--------------------------------------------------------------------------------
--          Converting NamedCExp
--------------------------------------------------------------------------------

-- used to convert data and type constructor tags
tag : Name -> Maybe Int -> Either Int Name
tag n = maybe (Right n) Left

-- creates a single assignment statement.
assign : (e : Effect) -> Exp -> Stmt (Just e)
assign Returns          = Return
assign (ErrorWithout v) = Assign v

mutual
  getInteger : NamedCExp -> Maybe Integer
  getInteger (NmPrimVal _ $ BI x) = Just x
  getInteger x                    = integerArith x

  -- this is a local hack to fix #1320 for the JS backend
  -- the moste basic sequences of arithmetic `Integer` expressions
  -- are evaluated to prevent us from introducing slow
  -- cascades of (1n + ...) coming from small `Nat` literals.
  integerArith : NamedCExp -> Maybe Integer
  integerArith (NmOp _ (Add IntegerType) [x,y]) =
    [| getInteger x + getInteger y |]
  integerArith (NmOp _ (Mul IntegerType) [x,y]) =
    [| getInteger x * getInteger y |]
  integerArith _ = Nothing

mutual
  -- Converts a `NamedCExp` by calling `stmt` with a
  -- newly generated local variable.
  -- If the result is a single assignment statement
  -- and the given filter function returns a `Just a`,
  -- only result `a` is returned.
  -- If the result is more complex or the filter returns
  -- `Nothing`, the resulting block
  -- will be kept and a pointer to the new variable
  -- will be returned which can then be used for instance
  -- as a function's argument.
  lift :  { auto c : Ref ESs ESSt }
       -> NamedCExp
       -> (filter  : Exp -> Maybe a)
       -> (fromVar : Var -> a)
       -> Core (List (Stmt Nothing), a)
  lift n filter fromVar = do
    l <- nextLocal
    b <- stmt (ErrorWithout l) n
    let pair = ([declare b], fromVar l)
    case b of
      -- elaborator needed some help here
      Assign _ e => pure $ maybe pair (the (List _) [],) (filter e)
      _          => pure pair

  -- Convert and lift (if necessary, see comment for `lift`)
  -- a function argument. The filter function used to
  -- decide whether to keep or lift a function argument
  -- comes from the passed `ESSt` state and can therefore
  -- vary across backends.
  liftArg : { auto c : Ref ESs ESSt }
           -> NamedCExp
           -> Core (List (Stmt Nothing), Exp)
  liftArg x = do
    f <- isArg <$> get ESs
    lift x (\e => guard (f e) $> e) (EMinimal . MVar)

  -- Convert and lift (if necessary, see comment for `lift`)
  -- a function expression.
  liftFun : { auto c : Ref ESs ESSt }
           -> NamedCExp
           -> Core (List (Stmt Nothing), Exp)
  liftFun x = do
    f <- isFun <$> get ESs
    lift x (\e => guard (f e) $> e) (EMinimal . MVar)

  -- Convert and lift (if necessary, see comment for `liftArg`)
  -- a `Vect` of function arguments.
  liftArgsVect : { auto c : Ref ESs ESSt }
               -> Vect n NamedCExp
               -> Core (List (Stmt Nothing), Vect n Exp)
  liftArgsVect xs = do
    ps <- traverseVect liftArg xs
    pure (concatMap fst ps, map snd ps)

  -- Convert and lift (if necessary, see comment for `liftArg`)
  -- a `List` of function arguments.
  liftArgs : { auto c : Ref ESs ESSt }
           -> List NamedCExp
           -> Core (List (Stmt Nothing), List Exp)
  liftArgs xs = do
    ps <- traverse liftArg xs
    pure (concatMap fst ps, map snd ps)

  -- Convert and lift an expression. If the result is
  -- not a `Minimal` expression, an additional assignment statement is
  -- generated. This is used to lift the scrutinees of
  -- constructor case expressions to make sure they are
  -- only evluated once (see also PR #1494).
  liftMinimal : { auto c : Ref ESs ESSt }
              -> NamedCExp
              -> Core (List (Stmt Nothing), Minimal)
  liftMinimal n = lift n toMinimal MVar

  -- creates a (possibly multiargument) lambda.
  lambda : {auto c : Ref ESs ESSt} -> Name -> NamedCExp -> Core Exp
  lambda n x = go [n] x
    where go : List Name -> NamedCExp -> Core Exp
          go ns (NmLam _  n x) = go (n :: ns) x
          go ns x              = do
            vs <- traverse registerLocal (reverse ns)
            ELam vs <$> stmt Returns x

  -- convert a `NamedCExp` to a sequence of statements.
  export
  stmt :  {auto c : Ref ESs ESSt}
        -> (e : Effect)
        -> NamedCExp
        -> Core (Stmt $ Just e)
  -- a local name gets registered or resolved
  stmt e (NmLocal _ n) = assign e . EMinimal <$> getOrRegisterLocal n

  -- a function name gets registered or resolved
  stmt e (NmRef _ n) = assign e . EMinimal . MVar <$> getOrRegisterRef n

  stmt e (NmLam _ n x) = assign e <$> lambda n x

  -- in case of a let expression, we just generate two
  -- blocks of statements and concatenate them.
  -- We always introduce a new local variable for `n`,
  -- since a variable called `n` might be used in both blocks.
  stmt e (NmLet _ n y z) = do
    v  <- nextLocal
    b1 <- stmt (ErrorWithout v) y
    addLocal n (MVar v)
    b2 <- stmt e z
    pure $ prepend [declare b1] b2

  -- when applying a function, we potentially need to
  -- lift both, the function expression itself and the argument
  -- list, to the surrounding scope.
  stmt e (NmApp _ x xs) = do
    (mbx, vx)    <- liftFun x
    (mbxs, args) <- liftArgs xs
    pure . prepend (mbx ++ mbxs) $ assign e (EApp vx args)

  stmt e (NmCon _ n ci tg xs) = do
    (mbxs, args) <- liftArgs xs
    pure . prepend mbxs $ assign e (ECon tg ci args)

  stmt e o@(NmOp _ x xs) =
    case integerArith o of
      Just n  => pure . assign e $ EPrimVal (BI n)
      Nothing => do
        (mbxs, args) <- liftArgsVect xs
        pure . prepend mbxs $ assign e (EOp x args)

  stmt e (NmExtPrim _ n xs) = do
    (mbxs, args) <- liftArgs xs
    pure . prepend mbxs $ assign e (EExtPrim n args)

  stmt e (NmForce _ _ x) = do
    (mbx, vx) <- liftFun x
    pure . prepend mbx $ assign e (EApp vx [])

  stmt e (NmDelay _ _ x) = assign e . ELam [] <$> stmt Returns x

  -- No need for a `switch` if we only have a single branch.
  -- It's still necessary to lift the scrutinee, however,
  -- since its fields might be accessed several times in
  -- the implementation of `x`.
  stmt e (NmConCase _ sc [x] Nothing) = do
    (mbx, vx) <- liftMinimal sc
    b         <- body <$> conAlt e vx x
    pure $ prepend mbx b

  -- No need for a `switch` statement if we only have
  -- a `default` branch.
  stmt e (NmConCase _ _  [] (Just x)) = stmt e x

  -- Create a `switch` statement from a pattern match
  -- on constructors. The scrutinee is lifted to the
  -- surrounding scope and memoized if necessary.
  stmt e (NmConCase _ sc xs x) = do
    (mbx, vx) <- liftMinimal sc
    alts      <- traverse (conAlt e vx) xs
    def       <- traverseOpt (stmt e) x
    pure . prepend mbx $ ConSwitch e vx alts def

  -- Pattern matches on constants behave very similar
  -- to the ones on constructors.
  stmt e (NmConstCase _ _  [x] Nothing) = body <$> constAlt e x
  stmt e (NmConstCase _ _  [] (Just x)) = stmt e x
  stmt e (NmConstCase _ sc xs x) = do
    (mbx, ex) <- liftArg sc
    alts      <- traverse (constAlt e) xs
    def       <- traverseOpt (stmt e) x
    pure . prepend mbx $ ConstSwitch e ex alts def

  stmt e (NmPrimVal _ x) = pure . assign e $ EPrimVal x

  stmt e (NmErased _)    = pure . assign e $ EErased

  stmt _ (NmCrash _ x)   = pure $ Error x

  -- a single branch in a pattern match on constructors
  conAlt :  { auto c : Ref ESs ESSt }
         -> (e         : Effect)
         -> (scrutinee : Minimal)
         -> NamedConAlt
         -> Core (EConAlt e)
  conAlt e sc (MkNConAlt n ci tg args x) = do
    -- We map the list of args to the corresponding
    -- data projections (field accessors). They'll
    -- be then properly inlined when converting `x`.
    projections sc args
    MkEConAlt tg ci <$> stmt e x

  -- a single branch in a pattern match on a constant
  constAlt :  { auto c : Ref ESs ESSt }
           -> (e : Effect)
           -> NamedConstAlt
           -> Core (EConstAlt e)
  constAlt e (MkNConstAlt c x) = MkEConstAlt c <$> stmt e x
