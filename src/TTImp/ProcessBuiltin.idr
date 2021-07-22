||| Checking a %builtin pragma is correct.
-- If we get more builtins it might be wise to move each builtin to it's own file.
module TTImp.ProcessBuiltin

import Data.List

import Libraries.Data.Fin as Libs
import Libraries.Data.NameMap

import Core.CaseTree
import Core.Core
import Core.Context
import Core.Context.Log
import Core.Env
import Core.Metadata
import Core.TT
import Core.UnifyState

import TTImp.TTImp

%default covering

showDefType : Def -> String
showDefType None = "undefined"
showDefType (PMDef {}) = "function"
showDefType (ExternDef {}) = "external function"
showDefType (ForeignDef {}) = "foreign function"
showDefType (Builtin {}) = "builtin function"
showDefType (DCon {}) = "data constructor"
showDefType (TCon {}) = "type constructor"
showDefType (Hole {}) = "hole"
showDefType (BySearch {}) = "search"
showDefType (Guess {}) = "guess"
showDefType ImpBind = "bound name"
showDefType Delayed = "delayed"

||| Get the return type.
getReturnType : {vars : _} -> Term vars -> Maybe (vars ** Term vars)
getReturnType tm@(Bind _ x b scope) = case b of
    Let _ _ val _ => getReturnType $ subst {x} val scope
    Pi _ _ _ _ => getReturnType scope
    _ => Nothing
getReturnType tm = Just (vars ** tm)

||| Get the top level type constructor if there is one.
getTypeCons : {vars : _} -> Term vars -> Maybe Name
getTypeCons (Local _ _ _ p) = Just $ nameAt p
getTypeCons (Ref _ _ name) = Just name
getTypeCons (Meta {}) = Nothing
getTypeCons (Bind _ x b scope) = case b of
    Let _ _ val _ => getTypeCons $ subst {x} val scope
    _ => Nothing
getTypeCons (App _ fn _) = getTypeCons fn
getTypeCons _ = Nothing

||| Get the arguments of a `Term` representing a type.
getTypeArgs : {vars : _} -> Term vars -> List (vars ** Term vars)
getTypeArgs (Bind _ x b tm) = case b of
    Let _ _ val _ => getTypeArgs $ subst {x} val tm
    Pi _ _ _ arg => (_ ** arg) :: getTypeArgs tm
    _ => []
getTypeArgs _ = []

||| Get all non-erased aruments.
getNEArgs : {vars : _} -> Term vars -> List (vars ** Term vars)
getNEArgs (Bind _ x b tm) = case b of
    Let _ _ val _ => getNEArgs $ subst {x} val tm
    Pi _ mul _ arg => if isErased mul
        then getNEArgs tm
        else (_ ** arg) :: getNEArgs tm
    _ => []
getNEArgs _ = []

||| Get the first non-erased argument type.
getFirstNEType : {vars : _} -> Term vars -> Maybe (vars ** Term vars)
getFirstNEType tm = case getNEArgs tm of
    [] => Nothing
    arg :: _ => Just arg

||| Get the index of the first non-erased argument if it exists.
getNEIndex : (arity : Nat) -> Term vars -> Maybe (Fin arity)
getNEIndex ar (Bind _ x b tm) = case b of
    Let _ _ val _ => getNEIndex ar $ subst {x} val tm
    Pi _ mul _ arg => if isErased mul
        then getNEIndex ar tm >>= Libs.strengthen . FS
        else natToFin 0 ar
    _ => Nothing
getNEIndex _ _ = Nothing

||| Get the index of all non-erased Integer argument.
getNEIntegerIndex : (arity : Nat) -> Term vars -> Maybe (List (Fin arity))
getNEIntegerIndex ar (Bind _ x b tm) = case b of
    Let _ _ val _ => getNEIntegerIndex ar $ subst {x} val tm
    Pi _ mul _ arg => if isRigOther mul && isInteger arg
        then case natToFin 0 ar of
            Nothing => Nothing
            Just idx => map (Prelude.(::) idx) $ go ar tm
        else go ar tm
    _ => Nothing
  where
    isInteger : forall vars. Term vars -> Bool
    isInteger (PrimVal _ IntegerType) = True
    isInteger _ = False
    go : forall vars. (sarity : Nat) -> Term vars -> Maybe (List (Fin sarity))
    go (S ar) tm = map FS <$> getNEIntegerIndex ar tm
    go Z _ = Just []
getNEIntegerIndex _ _ = Just []

||| Do the terms match ignoring arguments to type constructors.
termConMatch : Term vs -> Term vs' -> Bool
termConMatch (Local _ _ x _) (Local _ _ y _) = x == y
termConMatch (Ref _ _ n) (Ref _ _ m) = n == m
termConMatch (Meta _ _ i args0) (Meta _ _ j args1)
    = i == j && all (uncurry termConMatch) (zip args0 args1)
    -- I don't understand how they're equal if args are different lengths
    -- but this is what's in Core.TT.
termConMatch (Bind _ _ b s) (Bind _ _ c t) = eqBinderBy termConMatch b c && termConMatch s t
termConMatch (App _ f _) (App _ g _) = termConMatch f g
termConMatch (As _ _ a p) (As _ _ b q) = termConMatch a b && termConMatch p q
termConMatch (TDelayed _ _ tm0) tm1 = termConMatch tm0 tm1
termConMatch tm0 (TDelayed _ _ tm1) = termConMatch tm0 tm1
    -- don't check for laziness here to give more accurate error messages.
termConMatch (TDelay _ _ tm0 x0) (TDelay _ _ tm1 x1) = termConMatch tm0 tm1 && termConMatch x0 x1
termConMatch (TForce _ _ tm0) tm1 = termConMatch tm0 tm1
termConMatch tm0 (TForce _ _ tm1) = termConMatch tm0 tm1
termConMatch (PrimVal _ _) (PrimVal _ _) = True -- no constructor to check.
termConMatch (Erased _ _) (Erased _ _) = True -- return type can't erased?
termConMatch (TType _) (TType _) = True
termConMatch _ _ = False

||| Check a type is strict.
isStrict : Term vs -> Bool
isStrict (Local _ _ _ _) = True
isStrict (Ref _ _ _) = True
isStrict (Meta _ _ i args) = all isStrict args
isStrict (Bind _ _ b s) = isStrict (binderType b) && isStrict s
isStrict (App _ f x) = isStrict f && isStrict x
isStrict (As _ _ a p) = isStrict a && isStrict p
isStrict (TDelayed _ _ _) = False
isStrict (TDelay _ _ f x) = isStrict f && isStrict x
isStrict (TForce _ _ tm) = isStrict tm
isStrict (PrimVal _ _) = True
isStrict (Erased _ _) = True
isStrict (TType _) = True

getNatBuiltin : Ref Ctxt Defs => Name -> Core (Maybe NatBuiltin)
getNatBuiltin n = do
    n' <- getFullName n
    lookup n' . natTyNames . builtinTransforms <$> get Ctxt

||| Get the name and arity (of non-erased arguments only) of a list of names.
||| `cons` should all be data constructors (`DCon`) otherwise it will throw an error.
getConsGDef : Context -> FC -> (cons : List Name) -> Core $ List (Name, GlobalDef)
getConsGDef c fc = traverse $ \n => do
    [(n', _, gdef)] <- lookupCtxtName n c
        | [] => throw $ UndefinedName fc n
        | ns => throw $ AmbiguousName fc $ (\(n, _, _) => n) <$> ns
    pure (n', gdef)

||| Check a list of constructors has exactly
||| 1 'Z'-like constructor
||| and 1 `S`-like constructor, which has type `ty -> ty` or `ty arg -> `ty (f arg)`.
checkNatCons : Context -> (cons : List (Name, GlobalDef)) -> (dataType : Name) -> FC -> Core NatBuiltin
checkNatCons c cons ty fc = case !(foldr checkCon (pure (Nothing, Nothing)) cons) of
    (Just zero, Just succ) => pure $ MkNatBuiltin {zero, succ}
    (Nothing, _) => throw $ GenericMsg fc $ "No 'Z'-like constructors for " ++ show ty ++ "."
    (_, Nothing) => throw $ GenericMsg fc $ "No 'S'-like constructors for " ++ show ty ++ "."
  where
    ||| Check if a list of names contains a name.
    checkSArgType : List Name -> Core ()
    checkSArgType [] = throw $ GenericMsg fc $ "'S'-like constructor for " ++ show ty ++ " is missing argument of type: " ++ show ty
    checkSArgType (n :: ns) = if nameRoot n == nameRoot ty && (n `matches` ty)
        then checkSArgType ns
        else throw $ GenericMsg fc $ "'S'-like constructor for " ++ show ty ++ " has unexpected argument: " ++ show n

    ||| Check the type of an 'S'-like constructor.
    checkTyS : Name -> GlobalDef -> Core ()
    checkTyS n gdef = do
        let type = gdef.type
            erase = gdef.eraseArgs
        let Just (_ ** arg) = getFirstNEType type
            | Nothing => throw $ InternalError "Expected a non-erased argument, found none."
        let Just (_ ** ret) = getReturnType type
            | Nothing => throw $ InternalError $ "Unexpected type " ++ show type
        unless (termConMatch arg ret) $ throw $ GenericMsg fc $ "Incorrect type for 'S'-like constructor for " ++ show ty ++ "."
        unless (isStrict arg) $ throw $ GenericMsg fc $ "Natural builtin does not support lazy types."
        pure ()

    ||| Check a constructor's arity and type.
    -- 'Z'-like constructor is always first, then 'S'-like constructor.
    checkCon : (Name, GlobalDef) -> Core (Maybe Name, Maybe Name) -> Core (Maybe Name, Maybe Name)
    checkCon (n, gdef) cons = do
        (zero, succ) <- cons
        let DCon _ arity _ = gdef.definition
            | def => throw $ GenericMsg fc $ "Expected data constructor, found:" ++ showDefType def
        case arity `minus` length gdef.eraseArgs of
            0 => case zero of
                Just _ => throw $ GenericMsg fc $ "Multiple 'Z'-like constructors for " ++ show ty ++ "."
                Nothing => pure (Just n, succ)
            1 => case succ of
                Just _ => throw $ GenericMsg fc $ "Multiple 'S'-like constructors for " ++ show ty ++ "."
                Nothing => do
                    checkTyS n gdef
                    pure (zero, Just n)
            _ => throw $ GenericMsg fc $ "Constructor " ++ show n ++ " doesn't match any pattern for Natural."

addBuiltinNat :
    Ref Ctxt Defs =>
    (ty : Name) -> NatBuiltin -> Core ()
addBuiltinNat type cons = do
    log "builtin.Natural.addTransform" 10
        $ "Add %builtin Natural transform for " ++ show type ++ "."
    update Ctxt $ record
        { builtinTransforms.natTyNames $= insert type cons
        , builtinTransforms.natZNames $= insert cons.zero MkZERO
        , builtinTransforms.natSNames $= insert cons.succ MkSUCC
        }

addNatToInteger :
    Ref Ctxt Defs =>
    (fn : Name) ->
    NatToInt ->
    Core ()
addNatToInteger fn nToI = do
    log "builtin.NaturalToInteger.addTransforms" 10
        $ "Add %builtin NaturalToInteger transform for " ++ show fn ++ "."
    update Ctxt $ record
        { builtinTransforms.natToIntegerFns $= insert fn nToI
        }

||| Check a `%builtin Natural` pragma is correct.
processBuiltinNatural :
    Ref Ctxt Defs =>
    Defs -> FC -> Name -> Core ()
processBuiltinNatural ds fc name = do
    log "builtin.Natural" 5 $ "Processing %builtin Natural " ++ show name ++ "."
    [(n, _, gdef)] <- lookupCtxtName name ds.gamma
        | [] => undefinedName fc name
        | ns => throw $ AmbiguousName fc $ (\(n, _, _) => n) <$> ns
    let TCon _ _ _ _ _ _ dcons _ = gdef.definition
        | def => throw $ GenericMsg fc
            $ "Expected a type constructor, found " ++ showDefType def ++ "."
    cons <- getConsGDef ds.gamma fc dcons
    cons <- checkNatCons ds.gamma cons n fc
    zero <- getFullName cons.zero
    succ <- getFullName cons.succ
    addBuiltinNat n $ MkNatBuiltin {zero, succ}

||| Check a `%builtin NaturalToInteger` pragma is correct.
processNatToInteger :
    Ref Ctxt Defs =>
    Defs -> FC -> Name -> Core ()
processNatToInteger ds fc fn = do
    log "builtin.NaturalToInteger" 5 $ "Processing %builtin NaturalToInteger " ++ show fn ++ "."
    [(n, _, gdef)] <- lookupCtxtName fn ds.gamma
        | [] => undefinedName fc fn
        | ns => throw $ AmbiguousName fc $ (\(n, _, _) => n) <$> ns
    let PMDef _ args _ cases _ = gdef.definition
        | def => throw $ GenericMsg fc
            $ "Expected function definition, found " ++ showDefType def ++ "."
    type <- toFullNames gdef.type
    logTerm "builtin.NaturalToInteger" 25 ("Type of " ++ show fn) type
    let [(_ ** arg)] = getNEArgs type
        | [] => throw $ GenericMsg fc $ "No arguments found for " ++ show n ++ "."
        | _ => throw $ GenericMsg fc $ "More than 1 non-erased arguments found for " ++ show n ++ "."
    let Just tyCon = getTypeCons arg
        | Nothing => throw $ GenericMsg fc
            $ "No type constructor found for non-erased arguement of " ++ show n ++ "."
    Just _ <- getNatBuiltin tyCon
        | Nothing => throw $ GenericMsg fc $ "Non-erased argument is not a 'Nat'-like type."
    let arity = length $ getTypeArgs type
    let Just natIdx = getNEIndex arity type
        | Nothing => throw $ InternalError "Couldn't find non-erased argument."
    addNatToInteger n (MkNatToInt arity natIdx)

addIntegerToNat :
    Ref Ctxt Defs =>
    (fn : Name) ->
    IntToNat ->
    Core ()
addIntegerToNat fn iToN = do
    log "builtin.IntegerToNatural.addTransforms" 10
        $ "Add %builtin IntegerToNatural transform for " ++ show fn ++ "."
    update Ctxt $ record
        { builtinTransforms.integerToNatFns $= insert fn iToN
        }

||| Check a `%builtin IntegerToNatural` pragma is correct.
processIntegerToNat :
    Ref Ctxt Defs =>
    Defs -> FC -> Name -> Core ()
processIntegerToNat ds fc fn = do
    log "builtin.IntegerToNatural" 5 $ "Processing %builtin IntegerToNatural " ++ show fn ++ "."
    [(n, _, gdef)] <- lookupCtxtName fn ds.gamma
        | [] => undefinedName fc fn
        | ns => throw $ AmbiguousName fc $ (\(n, _, _) => n) <$> ns
    type <- toFullNames gdef.type
    let PMDef _ args _ cases _ = gdef.definition
        | def => throw $ GenericMsg fc
            $ "Expected function definition, found " ++ showDefType def ++ "."
    let arity = length $ getTypeArgs type
    logTerm "builtin.IntegerToNatural" 25 ("Type of " ++ show fn) type
    let Just [intIdx] = getNEIntegerIndex arity type
        | Just [] => throw $ GenericMsg fc $ "No unrestricted arguments of type `Integer` found for " ++ show n ++ "."
        | Just _ => throw $ GenericMsg fc $ "More than one unrestricted arguments of type `Integer` found for " ++ show n ++ "."
        | Nothing => throw $ InternalError
            $ "Unexpected arity while processing %builtin IntegerToNatural " ++ show n ++ " (getNEIntegerIndex returned Nothing)"
    let Just (_ ** retTy) = getReturnType type
        | Nothing => throw $ InternalError $ "Unexpected type " ++ show type
    let Just retCon = getTypeCons retTy
        | Nothing => throw $ GenericMsg fc
            $ "No type constructor found for return type of " ++ show n ++ "."
    Just _ <- getNatBuiltin retCon
        | Nothing => throw $ GenericMsg fc $ "Return type is not a 'Nat'-like type"
    addIntegerToNat n (MkIntToNat arity intIdx)

||| Check a `%builtin` pragma is correct.
export
processBuiltin :
    Ref Ctxt Defs =>
    NestedNames vars -> Env Term vars -> FC -> BuiltinType -> Name -> Core ()
processBuiltin nest env fc type name = do
    ds <- get Ctxt
    case type of
        BuiltinNatural => processBuiltinNatural ds fc name
        NaturalToInteger => processNatToInteger ds fc name
        IntegerToNatural => processIntegerToNat ds fc name
