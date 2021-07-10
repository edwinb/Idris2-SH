module TTImp.Elab.App

import Core.CaseTree
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT
import Core.Value

import TTImp.Elab.Check
import TTImp.Elab.Dot
import TTImp.TTImp

import Data.List
import Data.List1
import Data.Maybe

%default covering

checkVisibleNS : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Visibility -> Core ()
checkVisibleNS fc (NS ns x) vis
    = if !(isVisible ns)
         then if !isAllPublic
                       || visibleInAny (!getNS :: !getNestedNS) (NS ns x) vis
                 then pure ()
                 else throw $ InvisibleName fc (NS ns x) Nothing
         else throw $ InvisibleName fc (NS ns x) (Just ns)
checkVisibleNS _ _ _ = pure ()

-- Get the type of a variable, assuming we haven't found it in the nested
-- names. Look in the Env first, then the global context.
getNameType : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto e : Ref EST (EState vars)} ->
              RigCount -> Env Term vars ->
              FC -> Name ->
              Core (Term vars, Glued vars)
getNameType rigc env fc x
    = case defined x env of
           Just (MkIsDefined rigb lv) =>
              do rigSafe rigb rigc
                 let binder = getBinder lv env
                 let bty = binderType binder

                 log "metadata.names" 7 $ "getNameType is adding ↓"
                 addNameType fc x env bty

                 when (isLinear rigb) $
                      do est <- get EST
                         put EST
                            (record { linearUsed $= ((MkVar lv) :: ) } est)
                 log "ide-mode.highlight" 8
                     $ "getNameType is trying to add Bound: "
                      ++ show x ++ " (" ++ show fc ++ ")"
                 when (isSourceName x) $
                   whenJust (isConcreteFC fc) \nfc => do
                     log "ide-mode.highlight" 7 $ "getNameType is adding Bound: " ++ show x
                     addSemanticDecorations [(nfc, Bound, Just x)]

                 pure (Local fc (Just (isLet binder)) _ lv, gnf env bty)
           Nothing =>
              do defs <- get Ctxt
                 [(pname, i, def)] <- lookupCtxtName x (gamma defs)
                      | [] => undefinedName fc x
                      | ns => throw (AmbiguousName fc (map fst ns))
                 checkVisibleNS fc (fullname def) (visibility def)
                 rigSafe (multiplicity def) rigc
                 let nt = case definition def of
                               PMDef _ _ _ _ _ => Func
                               DCon t a _ => DataCon t a
                               TCon t a _ _ _ _ _ _ => TyCon t a
                               _ => Func

                 log "ide-mode.highlight" 8
                     $ "getNameType is trying to add something for: "
                      ++ show def.fullname ++ " (" ++ show fc ++ ")"

                 when (isSourceName def.fullname) $
                   whenJust (isConcreteFC fc) \nfc => do
                     let decor = nameTypeDecoration nt
                     log "ide-mode.highlight" 7
                       $ "getNameType is adding " ++ show decor ++ ": " ++ show def.fullname
                     addSemanticDecorations [(nfc, decor, Just def.fullname)]

                 pure (Ref fc nt (Resolved i), gnf env (embed (type def)))
  where
    rigSafe : RigCount -> RigCount -> Core ()
    rigSafe lhs rhs = when (lhs < rhs)
                           (throw (LinearMisuse fc !(getFullName x) lhs rhs))

-- Get the type of a variable, looking it up in the nested names first.
getVarType : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto e : Ref EST (EState vars)} ->
             RigCount -> NestedNames vars -> Env Term vars ->
             FC -> Name ->
             Core (Term vars, Nat, Glued vars)
getVarType rigc nest env fc x
    = case lookup x (names nest) of
           Nothing => do (tm, ty) <- getNameType rigc env fc x
                         pure (tm, 0, ty)
           Just (nestn, argns, tmf) =>
              do defs <- get Ctxt
                 let arglen = length argns
                 let n' = fromMaybe x nestn
                 case !(lookupCtxtExact n' (gamma defs)) of
                      Nothing => undefinedName fc n'
                      Just ndef =>
                         let nt = case definition ndef of
                                       PMDef _ _ _ _ _ => Func
                                       DCon t a _ => DataCon t a
                                       TCon t a _ _ _ _ _ _ => TyCon t a
                                       _ => Func
                             tm = tmf fc nt
                             tyenv = useVars (getArgs tm)
                                             (embed (type ndef)) in
                             do checkVisibleNS fc (fullname ndef) (visibility ndef)
                                logTerm "elab" 5 ("Type of " ++ show n') tyenv
                                logTerm "elab" 5 ("Expands to") tm
                                log "elab" 5 $ "Arg length " ++ show arglen

                                -- Add the type to the metadata
                                log "metadata.names" 7 $ "getVarType is adding ↓"
                                addNameType fc x env tyenv

                                when (isSourceName ndef.fullname) $
                                  whenJust (isConcreteFC fc) \nfc => do
                                    let decor = nameTypeDecoration nt
                                    log "ide-mode.highlight" 7
                                       $ "getNameType is adding "++ show decor ++": "
                                                                 ++ show ndef.fullname
                                    addSemanticDecorations [(nfc, decor, Just ndef.fullname)]

                                pure (tm, arglen, gnf env tyenv)
    where
      useVars : {vars : _} ->
                List (Term vars) -> Term vars -> Term vars
      useVars [] sc = sc
      useVars (a :: as) (Bind bfc n (Pi fc c _ ty) sc)
           = Bind bfc n (Let fc c a ty) (useVars (map weaken as) sc)
      useVars as (Bind bfc n (Let fc c v ty) sc)
           = Bind bfc n (Let fc c v ty) (useVars (map weaken as) sc)
      useVars _ sc = sc -- Can't happen?

isHole : NF vars -> Bool
isHole (NApp _ (NMeta _ _ _) _) = True
isHole _ = False

mutual
  makeImplicit : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 RigCount -> RigCount -> ElabInfo ->
                 NestedNames vars -> Env Term vars ->
                 FC -> (fntm : Term vars) ->
                 Name -> NF vars -> (Defs -> Closure vars -> Core (NF vars)) ->
                 (argdata : (Maybe Name, Nat)) ->
                 (expargs : List RawImp) ->
                 (autoargs : List RawImp) ->
                 (namedargs : List (Name, RawImp)) ->
                 (knownret : Bool) ->
                 (expected : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
  makeImplicit rig argRig elabinfo nest env fc tm x aty sc (n, argpos) expargs autoargs namedargs kr expty
      = do defs <- get Ctxt
           nm <- genMVName x
           empty <- clearDefs defs
           metaty <- quote empty env aty
           metaval <- metaVar fc argRig env nm metaty
           let fntm = App fc tm metaval
           fnty <- sc defs (toClosure defaultOpts env metaval)
           when (bindingVars elabinfo) $
                do est <- get EST
                   put EST (addBindIfUnsolved nm argRig Implicit env metaval metaty est)
           checkAppWith rig elabinfo nest env fc
                        fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty

  makeAutoImplicit : {vars : _} ->
                     {auto c : Ref Ctxt Defs} ->
                     {auto m : Ref MD Metadata} ->
                     {auto u : Ref UST UState} ->
                     {auto e : Ref EST (EState vars)} ->
                     RigCount -> RigCount -> ElabInfo ->
                     NestedNames vars -> Env Term vars ->
                     FC -> (fntm : Term vars) ->
                     Name -> NF vars -> (Defs -> Closure vars -> Core (NF vars)) ->
                     (argpos : (Maybe Name, Nat)) ->
                     (expargs : List RawImp) ->
                     (autoargs : List RawImp) ->
                     (namedargs : List (Name, RawImp)) ->
                     (knownret : Bool) ->
                     (expected : Maybe (Glued vars)) ->
                     Core (Term vars, Glued vars)
  makeAutoImplicit rig argRig elabinfo nest env fc tm x aty sc (n, argpos) expargs autoargs namedargs kr expty
  -- on the LHS, just treat it as an implicit pattern variable.
  -- on the RHS, add a searchable hole
      = if metavarImp (elabMode elabinfo)
           then do defs <- get Ctxt
                   nm <- genMVName x
                   empty <- clearDefs defs
                   metaty <- quote empty env aty
                   metaval <- metaVar fc argRig env nm metaty
                   let fntm = App fc tm metaval
                   fnty <- sc defs (toClosure defaultOpts env metaval)
                   est <- get EST
                   put EST (addBindIfUnsolved nm argRig AutoImplicit env metaval metaty est)
                   checkAppWith rig elabinfo nest env fc
                                fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
           else do defs <- get Ctxt
                   nm <- genMVName x
                   -- We need the full normal form to check determining arguments
                   -- so we might as well calculate the whole thing now
                   metaty <- quote defs env aty
                   est <- get EST
                   lim <- getAutoImplicitLimit
                   metaval <- searchVar fc argRig lim (Resolved (defining est))
                                        env nest nm metaty
                   let fntm = App fc tm metaval
                   fnty <- sc defs (toClosure defaultOpts env metaval)
                   checkAppWith rig elabinfo nest env fc
                                fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
    where
      metavarImp : ElabMode -> Bool
      metavarImp (InLHS _) = True
      metavarImp InTransform = True
      metavarImp _ = False

  makeDefImplicit : {vars : _} ->
                    {auto c : Ref Ctxt Defs} ->
                    {auto m : Ref MD Metadata} ->
                    {auto u : Ref UST UState} ->
                    {auto e : Ref EST (EState vars)} ->
                    RigCount -> RigCount -> ElabInfo ->
                    NestedNames vars -> Env Term vars ->
                    FC -> (fntm : Term vars) ->
                    Name -> NF vars -> NF vars ->
                    (Defs -> Closure vars -> Core (NF vars)) ->
                    (argpos : (Maybe Name, Nat)) ->
                    (expargs : List RawImp) ->
                    (autoargs : List RawImp) ->
                    (namedargs : List (Name, RawImp)) ->
                    (knownret : Bool) ->
                    (expected : Maybe (Glued vars)) ->
                    Core (Term vars, Glued vars)
  makeDefImplicit rig argRig elabinfo nest env fc tm x arg aty sc (n, argpos) expargs autoargs namedargs kr expty
  -- on the LHS, just treat it as an implicit pattern variable.
  -- on the RHS, use the default
      = if metavarImp (elabMode elabinfo)
           then do defs <- get Ctxt
                   nm <- genMVName x
                   empty <- clearDefs defs
                   metaty <- quote empty env aty
                   metaval <- metaVar fc argRig env nm metaty
                   let fntm = App fc tm metaval
                   fnty <- sc defs (toClosure defaultOpts env metaval)
                   est <- get EST
                   put EST (addBindIfUnsolved nm argRig AutoImplicit env metaval metaty est)
                   checkAppWith rig elabinfo nest env fc
                                fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
           else do defs <- get Ctxt
                   empty <- clearDefs defs
                   aval <- quote empty env arg
                   let fntm = App fc tm aval
                   fnty <- sc defs (toClosure defaultOpts env aval)
                   checkAppWith rig elabinfo nest env fc
                                fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
    where
      metavarImp : ElabMode -> Bool
      metavarImp (InLHS _) = True
      metavarImp InTransform = True
      metavarImp _ = False

  -- Defer elaborating anything which will be easier given a known target
  -- type (ambiguity, cases, etc)
  needsDelayExpr : {auto c : Ref Ctxt Defs} ->
                   (knownRet : Bool) -> RawImp ->
                   Core Bool
  needsDelayExpr False _ = pure False
  needsDelayExpr True (IVar fc n)
      = do defs <- get Ctxt
           pure $ case !(lookupCtxtName n (gamma defs)) of
                       (_ :: _ :: _) => True
                       _ => False
  needsDelayExpr True (IApp _ f _) = needsDelayExpr True f
  needsDelayExpr True (IAutoApp _ f _) = needsDelayExpr True f
  needsDelayExpr True (INamedApp _ f _ _) = needsDelayExpr True f
  needsDelayExpr True (ILam _ _ _ _ _ _) = pure True
  needsDelayExpr True (ICase _ _ _ _) = pure True
  needsDelayExpr True (ILocal _ _ _) = pure True
  needsDelayExpr True (IUpdate _ _ _) = pure True
  needsDelayExpr True (IAlternative _ _ _) = pure True
  needsDelayExpr True (ISearch _ _) = pure True
  needsDelayExpr True (IRewrite _ _ _) = pure True
  needsDelayExpr True _ = pure False

  -- On the LHS, for any concrete thing, we need to make sure we know
  -- its type before we proceed so that we can reject it if the type turns
  -- out to be polymorphic
  needsDelayLHS : {auto c : Ref Ctxt Defs} ->
                  RawImp -> Core Bool
  needsDelayLHS (IVar fc n) = pure True
  needsDelayLHS (IApp _ f _) = needsDelayLHS f
  needsDelayLHS (IAutoApp _ f _) = needsDelayLHS f
  needsDelayLHS (INamedApp _ f _ _) = needsDelayLHS f
  needsDelayLHS (IAlternative _ _ _) = pure True
  needsDelayLHS (IAs _ _ _ _ t) = needsDelayLHS t
  needsDelayLHS (ISearch _ _) = pure True
  needsDelayLHS (IPrimVal _ _) = pure True
  needsDelayLHS (IType _) = pure True
  needsDelayLHS (IWithUnambigNames _ _ t) = needsDelayLHS t
  needsDelayLHS _ = pure False

  onLHS : ElabMode -> Bool
  onLHS (InLHS _) = True
  onLHS _ = False

  needsDelay : {auto c : Ref Ctxt Defs} ->
               ElabMode ->
               (knownRet : Bool) -> RawImp ->
               Core Bool
  needsDelay (InLHS _) _ tm = needsDelayLHS tm
  needsDelay _ kr tm = needsDelayExpr kr tm

  checkValidPattern :
    {vars : _} ->
    {auto c : Ref Ctxt Defs} ->
    {auto m : Ref MD Metadata} ->
    {auto u : Ref UST UState} ->
    {auto e : Ref EST (EState vars)} ->
    RigCount -> Env Term vars -> FC ->
    Term vars -> Glued vars ->
    Core (Term vars, Glued vars)
  checkValidPattern rig env fc tm ty
    = do log "elab.app.lhs" 50 $ "Checking that " ++ show tm ++ " is a valid pattern"
         case tm of
           Bind _ _ (Lam _ _ _ _)  _ => registerDot rig env fc NotConstructor tm ty
           _ => pure (tm, ty)

  dotErased : {auto c : Ref Ctxt Defs} -> (argty : NF vars) ->
              Maybe Name -> Nat -> ElabMode -> RigCount -> RawImp -> Core RawImp
  dotErased argty mn argpos (InLHS lrig ) rig tm
      = if not (isErased lrig) && isErased rig
          then do
            -- if the argument type aty has a single constructor, there's no need
            -- to dot it
            mconsCount <- countConstructors argty
            if mconsCount == Just 1 || mconsCount == Just 0
              then pure tm
              else
                -- if argpos is an erased position of 'n', leave it, otherwise dot if
                -- necessary
                do defs <- get Ctxt
                   Just gdef <- maybe (pure Nothing) (\n => lookupCtxtExact n (gamma defs)) mn
                        | Nothing => pure (dotTerm tm)
                   if argpos `elem` safeErase gdef
                      then pure tm
                      else pure $ dotTerm tm
          else pure tm
    where
      ||| Count the constructors of a fully applied concrete datatype
      countConstructors : NF vars -> Core (Maybe Nat)
      countConstructors (NTCon _ tycName _ n args) =
        if length args == n
        then do defs <- get Ctxt
                Just gdef <- lookupCtxtExact tycName (gamma defs)
                | Nothing => pure Nothing
                let (TCon _ _ _ _ _ _ datacons _) = gdef.definition
                | _ => pure Nothing
                pure (Just (length datacons))
        else pure Nothing
      countConstructors _ = pure Nothing

      dotTerm : RawImp -> RawImp
      dotTerm tm
          = case tm of
                 IMustUnify _ _ _ => tm
                 IBindVar _ _ => tm
                 Implicit _ _ => tm
                 IAs _ _ _ _ (IBindVar _ _) => tm
                 IAs _ _ _ _ (Implicit _ _) => tm
                 IAs fc nameFC p t arg => IAs fc nameFC p t (IMustUnify fc ErasedArg tm)
                 _ => IMustUnify (getFC tm) ErasedArg tm
  dotErased _ _ _ _ _ tm = pure tm

  -- Check the rest of an application given the argument type and the
  -- raw argument. We choose elaboration order depending on whether we know
  -- the return type now. If we know it, elaborate the rest of the
  -- application first and come back to it, because that might infer types
  -- for implicit arguments, which might in turn help with type-directed
  -- disambiguation when elaborating the argument.
  checkRestApp : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 RigCount -> RigCount -> ElabInfo ->
                 NestedNames vars -> Env Term vars ->
                 FC -> (fntm : Term vars) -> Name ->
                 (aty : NF vars) -> (sc : Defs -> Closure vars -> Core (NF vars)) ->
                 (argdata : (Maybe Name, Nat)) ->
                 (arg : RawImp) ->
                 (expargs : List RawImp) ->
                 (autoargs : List RawImp) ->
                 (namedargs : List (Name, RawImp)) ->
                 (knownret : Bool) ->
                 (expected : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
  checkRestApp rig argRig elabinfo nest env fc tm x aty sc
               (n, argpos) arg_in expargs autoargs namedargs knownret expty
     = do defs <- get Ctxt
          arg <- dotErased aty n argpos (elabMode elabinfo) argRig arg_in
          kr <- if knownret
                   then pure True
                   else do sc' <- sc defs (toClosure defaultOpts env (Erased fc False))
                           concrete defs env sc'
          if (isHole aty && kr) || !(needsDelay (elabMode elabinfo) kr arg_in) then do
             nm <- genMVName x
             empty <- clearDefs defs
             metaty <- quote empty env aty
             (idx, metaval) <- argVar (getFC arg) argRig env nm metaty
             let fntm = App fc tm metaval
             logNF "elab" 10 ("Delaying " ++ show nm ++ " " ++ show arg) env aty
             logTerm "elab" 10 "...as" metaval
             fnty <- sc defs (toClosure defaultOpts env metaval)
             (tm, gty) <- checkAppWith rig elabinfo nest env fc
                                       fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
             defs <- get Ctxt
             aty' <- nf defs env metaty
             logNF "elab" 10 ("Now trying " ++ show nm ++ " " ++ show arg) env aty'

             -- On the LHS, checking an argument can't resolve its own type,
             -- it must be resolved from elsewhere. Otherwise we might match
             -- on things which are too specific for their polymorphic type.
             when (onLHS (elabMode elabinfo)) $
                case aty' of
                     NApp _ (NMeta _ i _) _ =>
                          do Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
                                  | Nothing => pure ()
                             when (isErased (multiplicity gdef)) $ addNoSolve i
                     _ => pure ()
             res <- check argRig (record { topLevel = False } elabinfo) nest env arg (Just $ glueBack defs env aty')
             when (onLHS (elabMode elabinfo)) $
                case aty' of
                     NApp _ (NMeta _ i _) _ => removeNoSolve i
                     _ => pure ()

             (argv, argt) <-
               if not (onLHS (elabMode elabinfo))
                 then pure res
                 else do let (argv, argt) = res
                         checkValidPattern rig env fc argv argt

             defs <- get Ctxt
             -- If we're on the LHS, reinstantiate it with 'argv' because it
             -- *may* have as patterns in it and we need to retain them.
             -- (As patterns are a bit of a hack but I don't yet see a
             -- better way that leads to good code...)
             logTerm "elab" 10 ("Solving " ++ show metaval ++ " with") argv
             ok <- solveIfUndefined env metaval argv
             -- If there's a constraint, make a constant, but otherwise
             -- just return the term as expected
             tm <- if not ok
                      then do res <- convert fc elabinfo env (gnf env metaval)
                                                 (gnf env argv)
                              let [] = constraints res
                                  | cs => do tmty <- getTerm gty
                                             newConstant fc rig env tm tmty cs
                              pure tm
                      else pure tm
             case elabMode elabinfo of
                  InLHS _ => -- reset hole and redo it with the unexpanded definition
                     do updateDef (Resolved idx) (const (Just (Hole 0 (holeInit False))))
                        ignore $ solveIfUndefined env metaval argv
                  _ => pure ()
             removeHole idx
             pure (tm, gty)
           else do
             logNF "elab" 10 ("Argument type " ++ show x) env aty
             logNF "elab" 10 ("Full function type") env
                      (NBind fc x (Pi fc argRig Explicit aty) sc)
             logC "elab" 10
                     (do ety <- maybe (pure Nothing)
                                     (\t => pure (Just !(toFullNames!(getTerm t))))
                                     expty
                         pure ("Overall expected type: " ++ show ety))
             res <- check argRig (record { topLevel = False } elabinfo)
                                   nest env arg (Just (glueBack defs env aty))
             (argv, argt) <-
               if not (onLHS (elabMode elabinfo))
                 then pure res
                 else do let (argv, argt) = res
                         checkValidPattern rig env fc argv argt

             logGlueNF "elab" 10 "Got arg type" env argt
             defs <- get Ctxt
             let fntm = App fc tm argv
             fnty <- sc defs (toClosure defaultOpts env argv)
             checkAppWith rig elabinfo nest env fc
                          fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty

  export
  findNamed : Name -> List (Name, RawImp) -> Maybe ((Name, RawImp), List (Name, RawImp))
  findNamed n l = case partition ((== n) . fst) l of
                       (x :: xs, ys) => Just (x, (xs ++ ys))
                       _ => Nothing

  export
  findBindAllExpPattern : List (Name, RawImp) -> Maybe RawImp
  findBindAllExpPattern = lookup (UN "_")

  isImplicitAs : RawImp -> Bool
  isImplicitAs (IAs _ _ UseLeft _ (Implicit _ _)) = True
  isImplicitAs _ = False

  isBindAllExpPattern : Name -> Bool
  isBindAllExpPattern (UN "_") = True
  isBindAllExpPattern _ = False

  -- Check an application of 'fntm', with type 'fnty' to the given list
  -- of explicit and implicit arguments.
  -- Returns the checked term and its (weakly) normalised type
  checkAppWith' : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 RigCount -> ElabInfo ->
                 NestedNames vars -> Env Term vars ->
                 FC -> (fntm : Term vars) -> (fnty : NF vars) ->
                 (argdata : (Maybe Name, Nat)) ->
                      -- function we're applying, and argument position, for
                      -- checking if it's okay to erase against 'safeErase'
                 (expargs : List RawImp) ->
                 (autoargs : List RawImp) ->
                 (namedargs : List (Name, RawImp)) ->
                 (knownret : Bool) -> -- Do we know what the return type is yet?
                              -- if we do, we might be able to use it to work
                              -- out the types of arguments before elaborating them
                 (expected : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
   -- Explicit Pi, we use provided unnamed explicit argument
  checkAppWith' rig elabinfo nest env fc tm ty@(NBind tfc x (Pi _ rigb Explicit aty) sc)
               argdata (arg :: expargs') autoargs namedargs kr expty
     = do let argRig = rig |*| rigb
          checkRestApp rig argRig elabinfo nest env fc
                       tm x aty sc argdata arg expargs' autoargs namedargs kr expty
  checkAppWith' rig elabinfo nest env fc tm ty@(NBind tfc x (Pi _ rigb Explicit aty) sc)
               argdata [] autoargs namedargs kr expty with (findNamed x namedargs)
   -- We found a compatible named argument
   checkAppWith' rig elabinfo nest env fc tm ty@(NBind tfc x (Pi _ rigb Explicit aty) sc)
                argdata [] autoargs namedargs kr expty | Just ((_, arg), namedargs')
    = do let argRig = rig |*| rigb
         checkRestApp rig argRig elabinfo nest env fc
                      tm x aty sc argdata arg [] autoargs namedargs' kr expty
   checkAppWith' rig elabinfo nest env fc tm ty@(NBind tfc x (Pi _ rigb Explicit aty) sc)
                argdata [] autoargs namedargs kr expty | Nothing
    = case findBindAllExpPattern namedargs of
           Just arg => -- Bind-all-explicit pattern is present - implicitly bind
             do let argRig = rig |*| rigb
                checkRestApp rig argRig elabinfo nest env fc
                             tm x aty sc argdata arg [] autoargs namedargs kr expty
           _ =>
             do defs <- get Ctxt
                if all isImplicitAs (autoargs
                                      ++ map snd (filter (not . isBindAllExpPattern . fst) namedargs))
                                                                    -- Only non-user implicit `as` bindings added by
                                                                    -- the compiler are allowed here
                   then -- We are done
                        checkExp rig elabinfo env fc tm (glueBack defs env ty) expty
                   else -- Some user defined binding is present while we are out of explicit arguments, that's an error
                        throw (InvalidArgs fc env (map (const (UN "<auto>")) autoargs ++ map fst namedargs) tm)
  -- Function type is delayed, so force the term and continue
  checkAppWith' rig elabinfo nest env fc tm (NDelayed dfc r ty@(NBind _ _ (Pi _ _ _ _) sc)) argdata expargs autoargs namedargs kr expty
      = checkAppWith' rig elabinfo nest env fc (TForce dfc r tm) ty argdata expargs autoargs namedargs kr expty
  -- If there's no more arguments given, and the plicities of the type and
  -- the expected type line up, stop
  checkAppWith' rig elabinfo nest env fc tm ty@(NBind tfc x (Pi _ rigb Implicit aty) sc)
               argdata [] [] [] kr (Just expty_in)
      = do let argRig = rig |*| rigb
           expty <- getNF expty_in
           defs <- get Ctxt
           case expty of
                NBind tfc' x' (Pi _ rigb' Implicit aty') sc'
                   => checkExp rig elabinfo env fc tm (glueBack defs env ty) (Just expty_in)
                _ => if not (preciseInf elabinfo)
                        then makeImplicit rig argRig elabinfo nest env fc tm x aty sc argdata [] [] [] kr (Just expty_in)
                        -- in 'preciseInf' mode blunder on anyway, and hope
                        -- that we can resolve the implicits
                        else handle (checkExp rig elabinfo env fc tm (glueBack defs env ty) (Just expty_in))
                               (\err => makeImplicit rig argRig elabinfo nest env fc tm x aty sc argdata [] [] [] kr (Just expty_in))
  -- Same for auto
  checkAppWith' rig elabinfo nest env fc tm ty@(NBind tfc x (Pi _ rigb AutoImplicit aty) sc)
               argdata [] [] [] kr (Just expty_in)
      = do let argRig = rig |*| rigb
           expty <- getNF expty_in
           defs <- get Ctxt
           case expty of
                NBind tfc' x' (Pi _ rigb' AutoImplicit aty') sc'
                   => checkExp rig elabinfo env fc tm (glueBack defs env ty) (Just expty_in)
                _ => makeAutoImplicit rig argRig elabinfo nest env fc tm x aty sc argdata [] [] [] kr (Just expty_in)
  -- Same for default
  checkAppWith' rig elabinfo nest env fc tm ty@(NBind tfc x (Pi _ rigb (DefImplicit aval) aty) sc)
               argdata [] [] [] kr (Just expty_in)
      = do let argRig = rigMult rig rigb
           expty <- getNF expty_in
           defs <- get Ctxt
           case expty of
                NBind tfc' x' (Pi _ rigb' (DefImplicit aval') aty') sc'
                   => if !(convert defs env aval aval')
                         then checkExp rig elabinfo env fc tm (glueBack defs env ty) (Just expty_in)
                         else makeDefImplicit rig argRig elabinfo nest env fc tm x aval aty sc argdata [] [] [] kr (Just expty_in)
                _ => makeDefImplicit rig argRig elabinfo nest env fc tm x aval aty sc argdata [] [] [] kr (Just expty_in)

  -- Check next unnamed auto implicit argument
  checkAppWith' rig elabinfo nest env fc tm (NBind tfc x (Pi _ rigb AutoImplicit aty) sc)
               argdata expargs (arg :: autoargs') namedargs kr expty
      = checkRestApp rig (rig |*| rigb) elabinfo nest env fc
                         tm x aty sc argdata arg expargs autoargs' namedargs kr expty
  -- Check next named auto implicit argument
  checkAppWith' rig elabinfo nest env fc tm (NBind tfc x (Pi _ rigb AutoImplicit aty) sc)
               argdata expargs [] namedargs kr expty
      = let argRig = rig |*| rigb in
            case findNamed x namedargs of
                 Just ((_, arg), namedargs') =>
                    checkRestApp rig argRig elabinfo nest env fc
                                 tm x aty sc argdata arg expargs [] namedargs' kr expty
                 Nothing =>
                         makeAutoImplicit rig argRig elabinfo nest env fc tm
                                              x aty sc argdata expargs [] namedargs kr expty
  -- Check next implicit argument
  checkAppWith' rig elabinfo nest env fc tm (NBind tfc x (Pi _ rigb Implicit aty) sc)
               argdata expargs autoargs namedargs kr expty
      = let argRig = rig |*| rigb in
            case findNamed x namedargs of
               Nothing => makeImplicit rig argRig elabinfo nest env fc tm
                                       x aty sc argdata expargs autoargs namedargs kr expty
               Just ((_, arg), namedargs') =>
                     checkRestApp rig argRig elabinfo nest env fc
                                  tm x aty sc argdata arg expargs autoargs namedargs' kr expty
  -- Check next default argument
  checkAppWith' rig elabinfo nest env fc tm (NBind tfc x (Pi _ rigb (DefImplicit arg) aty) sc)
               argdata expargs autoargs namedargs kr expty
      = let argRig = rigMult rig rigb in
            case findNamed x namedargs of
               Nothing => makeDefImplicit rig argRig elabinfo nest env fc tm
                                          x arg aty sc argdata expargs autoargs namedargs kr expty
               Just ((_, arg), namedargs') =>
                     checkRestApp rig argRig elabinfo nest env fc
                                  tm x aty sc argdata arg expargs autoargs namedargs' kr expty
  -- Invent a function type if we have extra explicit arguments but type is further unknown
  checkAppWith' {vars} rig elabinfo nest env fc tm ty (n, argpos) (arg :: expargs) autoargs namedargs kr expty
      = -- Invent a function type,  and hope that we'll know enough to solve it
        -- later when we unify with expty
        do logNF "elab.with" 10 "Function type" env ty
           logTerm "elab.with" 10 "Function " tm
           argn <- genName "argTy"
           retn <- genName "retTy"
           argTy <- metaVar fc erased env argn (TType fc)
           let argTyG = gnf env argTy
           retTy <- metaVar -- {vars = argn :: vars}
                            fc erased env -- (Pi RigW Explicit argTy :: env)
                            retn (TType fc)
           (argv, argt) <- check rig elabinfo
                                 nest env arg (Just argTyG)
           let fntm = App fc tm argv
           defs <- get Ctxt
           fnty <- nf defs env retTy -- (Bind fc argn (Let RigW argv argTy) retTy)
           let expfnty = gnf env (Bind fc argn (Pi fc top Explicit argTy) (weaken retTy))
           logGlue "elab.with" 10 "Expected function type" env expfnty
           whenJust expty (logGlue "elab.with" 10 "Expected result type" env)
           res <- checkAppWith' rig elabinfo nest env fc fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
           cres <- Check.convert fc elabinfo env (glueBack defs env ty) expfnty
           let [] = constraints cres
              | cs => do cty <- getTerm expfnty
                         ctm <- newConstant fc rig env (fst res) cty cs
                         pure (ctm, gnf env retTy)
           pure res
  -- Only non-user implicit `as` bindings are allowed to be present as arguments at this stage
  checkAppWith' rig elabinfo nest env fc tm ty argdata [] autoargs namedargs kr expty
      = do defs <- get Ctxt
           if all isImplicitAs (autoargs ++ map snd (filter (not . isBindAllExpPattern . fst) namedargs))
              then checkExp rig elabinfo env fc tm (glueBack defs env ty) expty
              else throw (InvalidArgs fc env (map (const (UN "<auto>")) autoargs ++ map fst namedargs) tm)

  ||| Entrypoint for checkAppWith: run the elaboration first and, if we're
  ||| on the LHS and the result is an under-applied constructor then insist
  ||| that it ought to be forced by another pattern somewhere else in the LHS.
  checkAppWith : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 RigCount -> ElabInfo ->
                 NestedNames vars -> Env Term vars ->
                 FC -> (fntm : Term vars) -> (fnty : NF vars) ->
                 (argdata : (Maybe Name, Nat)) ->
                      -- function we're applying, and argument position, for
                      -- checking if it's okay to erase against 'safeErase'
                 (expargs : List RawImp) ->
                 (autoargs : List RawImp) ->
                 (namedargs : List (Name, RawImp)) ->
                 (knownret : Bool) -> -- Do we know what the return type is yet?
                              -- if we do, we might be able to use it to work
                              -- out the types of arguments before elaborating them
                 (expected : Maybe (Glued vars)) ->
                 Core (Term vars, Glued vars)
  checkAppWith rig info nest env fc tm ty
    argdata expargs autoargs namedargs knownret expected
    = do res <- checkAppWith' rig info nest env fc tm ty
                   argdata expargs autoargs namedargs knownret expected
         let Just _ = isLHS (elabMode info)
               | Nothing => pure res
         let (Ref _ t _, args) = getFnArgs (fst res)
               | _ => pure res
         let Just (_, a) = isCon t
               | _ => pure res
         if a == length args
           then pure res
           else registerDot rig env fc UnderAppliedCon (fst res) (snd res)

export
checkApp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> ElabInfo ->
           NestedNames vars -> Env Term vars ->
           FC -> (fn : RawImp) ->
           (expargs : List RawImp) ->
           (autoargs : List RawImp) ->
           (namedargs : List (Name, RawImp)) ->
           Maybe (Glued vars) ->
           Core (Term vars, Glued vars)
checkApp rig elabinfo nest env fc (IApp fc' fn arg) expargs autoargs namedargs exp
   = checkApp rig elabinfo nest env fc' fn (arg :: expargs) autoargs namedargs exp
checkApp rig elabinfo nest env fc (IAutoApp fc' fn arg) expargs autoargs namedargs exp
   = checkApp rig elabinfo nest env fc' fn expargs (arg :: autoargs) namedargs exp
checkApp rig elabinfo nest env fc (INamedApp fc' fn nm arg) expargs autoargs namedargs exp
   = checkApp rig elabinfo nest env fc' fn expargs autoargs ((nm, arg) :: namedargs) exp
checkApp rig elabinfo nest env fc (IVar fc' n) expargs autoargs namedargs exp
   = do (ntm, arglen, nty_in) <- getVarType rig nest env fc' n
        nty <- getNF nty_in
        prims <- getPrimitiveNames
        elabinfo <- updateElabInfo prims (elabMode elabinfo) n expargs elabinfo

        addNameLoc fc' n

        logC "elab" 10
                (do defs <- get Ctxt
                    fnty <- quote defs env nty
                    exptyt <- maybe (pure Nothing)
                                       (\t => do ety <- getTerm t
                                                 etynf <- normaliseHoles defs env ety
                                                 pure (Just !(toFullNames etynf)))
                                       exp
                    pure ("Checking application of " ++ show !(getFullName n) ++
                          " (" ++ show n ++ ")" ++
                          " to " ++ show expargs ++ "\n\tFunction type " ++
                          (show !(toFullNames fnty)) ++ "\n\tExpected app type "
                                ++ show exptyt))
        let fn = case lookup n (names nest) of
                      Just (Just n', _) => n'
                      _ => n
        normalisePrims prims env
           !(checkAppWith rig elabinfo nest env fc ntm nty (Just fn, arglen) expargs autoargs namedargs False exp)
  where

    -- If the term is an application of a primitive conversion (fromInteger etc)
    -- and it's applied to a constant, fully normalise the term.
    normalisePrims : {vs : _} ->
                     List Name -> Env Term vs ->
                     (Term vs, Glued vs) ->
                     Core (Term vs, Glued vs)
    normalisePrims prims env res =
        do tm <- normalisePrimsOrPattern (`boundSafe` elabMode elabinfo) isIPrimVal
                                         (case elabMode elabinfo of
                                               InLHS _ => True
                                               _ => False)
                                         prims n expargs (fst res) env
           pure (fromMaybe (fst res) tm, snd res)

      where

        boundSafe : Constant -> ElabMode -> Bool
        boundSafe _ (InLHS _) = True -- always need to expand on LHS
        boundSafe (BI x) _ = abs x < 100 -- only do this for relatively small bounds.
                           -- Once it gets too big, we might be making the term
                           -- bigger than it would have been without evaluating!
        boundSafe _ _ = True


    updateElabInfo : List Name -> ElabMode -> Name ->
                     List RawImp -> ElabInfo -> Core ElabInfo
    -- If it's a primitive function applied to a constant on the LHS, treat it
    -- as an expression because we'll normalise the function away and match on
    -- the result
    updateElabInfo prims (InLHS _) n [IPrimVal fc c] elabinfo =
        do if elem (dropNS !(getFullName n)) prims
              then pure (record { elabMode = InExpr } elabinfo)
              else pure elabinfo
    updateElabInfo _ _ _ _ info = pure info

checkApp rig elabinfo nest env fc fn expargs autoargs namedargs exp
   = do (fntm, fnty_in) <- checkImp rig elabinfo nest env fn Nothing
        fnty <- getNF fnty_in
        checkAppWith rig elabinfo nest env fc fntm fnty (Nothing, 0) expargs autoargs namedargs False exp
