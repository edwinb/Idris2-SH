module TTImp.Elab.Case

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
import TTImp.Elab.Delayed
import TTImp.Elab.ImplicitBind
import TTImp.Elab.Utils
import TTImp.TTImp
import TTImp.Utils

import Data.List
import Data.Maybe
import Libraries.Data.NameMap

%default covering

export
changeVar : (old : Var vs) -> (new : Var vs) -> Term vs -> Term vs
changeVar (MkVar {i=x} old) (MkVar new) (Local fc r idx p)
    = if x == idx
         then Local fc r _ new
         else Local fc r _ p
changeVar old new (Meta fc nm i args)
    = Meta fc nm i (map (changeVar old new) args)
changeVar (MkVar old) (MkVar new) (Bind fc x b sc)
    = Bind fc x (assert_total (map (changeVar (MkVar old) (MkVar new)) b))
           (changeVar (MkVar (Later old)) (MkVar (Later new)) sc)
changeVar old new (App fc fn arg)
    = App fc (changeVar old new fn) (changeVar old new arg)
changeVar old new (As fc s nm p)
    = As fc s (changeVar old new nm) (changeVar old new p)
changeVar old new (TDelayed fc r p)
    = TDelayed fc r (changeVar old new p)
changeVar old new (TDelay fc r t p)
    = TDelay fc r (changeVar old new t) (changeVar old new p)
changeVar old new (TForce fc r p)
    = TForce fc r (changeVar old new p)
changeVar old new tm = tm

findLater : (x : Name) -> (newer : List Name) -> Var (newer ++ x :: older)
findLater x [] = MkVar First
findLater {older} x (_ :: xs)
    = let MkVar p = findLater {older} x xs in
          MkVar (Later p)

toRig1 : {idx : Nat} -> (0 p : IsVar nm idx vs) -> Env Term vs -> Env Term vs
toRig1 First (b :: bs)
    = if isErased (multiplicity b)
         then setMultiplicity b linear :: bs
         else b :: bs
toRig1 (Later p) (b :: bs) = b :: toRig1 p bs

toRig0 : {idx : Nat} -> (0 p : IsVar nm idx vs) -> Env Term vs -> Env Term vs
toRig0 First (b :: bs) = setMultiplicity b erased :: bs
toRig0 (Later p) (b :: bs) = b :: toRig0 p bs

-- When we abstract over the evironment, pi needs to be explicit
explicitPi : Env Term vs -> Env Term vs
explicitPi (Pi fc c _ ty :: env) = Pi fc c Explicit ty :: explicitPi env
explicitPi (b :: env) = b :: explicitPi env
explicitPi [] = []

allow : Maybe (Var vs) -> Env Term vs -> Env Term vs
allow Nothing env = env
allow (Just (MkVar p)) env = toRig1 p env

-- If the name is used elsewhere, update its multiplicity so it's
-- not required to be used in the case block
updateMults : List (Var vs) -> Env Term vs -> Env Term vs
updateMults [] env = env
updateMults (MkVar p :: us) env = updateMults us (toRig0 p env)

findImpsIn : {vars : _} ->
             FC -> Env Term vars -> List (Name, Term vars) -> Term vars ->
             Core ()
findImpsIn fc env ns (Bind _ n b@(Pi _ _ Implicit ty) sc)
    = findImpsIn fc (b :: env)
                 ((n, weaken ty) :: map (\x => (fst x, weaken (snd x))) ns)
                 sc
findImpsIn fc env ns (Bind _ n b sc)
    = findImpsIn fc (b :: env)
                 (map (\x => (fst x, weaken (snd x))) ns)
                 sc
findImpsIn fc env ns ty
    = when (not (isNil ns)) $
           throw (TryWithImplicits fc env (reverse ns))

merge : {vs : List Name} ->
        List (Var vs) -> List (Var vs) -> List (Var vs)
merge [] xs = xs
merge (v :: vs) xs
    = merge vs (v :: filter (not . sameVar v) xs)

-- Extend the list of variables we need in the environment so far, removing
-- duplicates
extendNeeded : {vs : _} ->
               Binder (Term vs) ->
               Env Term vs -> List (Var vs) -> List (Var vs)
extendNeeded (Let _ _ ty val) env needed
    = merge (findUsedLocs env ty) (merge (findUsedLocs env val) needed)
extendNeeded (PLet _ _ ty val) env needed
    = merge (findUsedLocs env ty) (merge (findUsedLocs env val) needed)
extendNeeded b env needed
    = merge (findUsedLocs env (binderType b)) needed

isNeeded : Nat -> List (Var vs) -> Bool
isNeeded x [] = False
isNeeded x (MkVar {i} _ :: xs) = x == i || isNeeded x xs

findScrutinee : {vs : _} ->
                Env Term vs -> RawImp -> Maybe (Var vs)
findScrutinee {vs = n' :: _} (b :: bs) (IVar loc' n)
    = if n' == n && not (isLet b)
         then Just (MkVar First)
         else do MkVar p <- findScrutinee bs (IVar loc' n)
                 Just (MkVar (Later p))
findScrutinee _ _ = Nothing

getNestData : (Name, (Maybe Name, List (Var vars), a)) ->
              (Name, Maybe Name, List (Var vars))
getNestData (n, (mn, enames, _)) = (n, mn, enames)

bindCaseLocals : FC -> List (Name, Maybe Name, List (Var vars)) ->
                 List (Name, Name)-> RawImp -> RawImp
bindCaseLocals fc [] args rhs = rhs
bindCaseLocals fc ((n, mn, envns) :: rest) argns rhs
    = -- trace ("Case local " ++ show (n,mn,envns) ++ " from " ++ show argns) $
        ICaseLocal fc n (fromMaybe n mn)
                 (map getNameFrom envns)
                 (bindCaseLocals fc rest argns rhs)
  where
    getArg : List (Name, Name) -> Nat -> Maybe Name
    getArg [] _ = Nothing
    getArg ((_, x) :: xs) Z = Just x
    getArg (x :: xs) (S k) = getArg xs k

    getNameFrom : Var vars -> Name
    getNameFrom (MkVar {i} _)
        = case getArg argns i of
               Nothing => n
               Just n' => n'

export
caseBlock : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount ->
            ElabInfo -> FC ->
            NestedNames vars ->
            Env Term vars ->
            RawImp -> -- original scrutinee
            Term vars -> -- checked scrutinee
            Term vars -> -- its type
            RigCount -> -- its multiplicity
            List ImpClause -> Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
caseBlock {vars} rigc elabinfo fc nest env scr scrtm scrty caseRig alts expected
    = do -- TODO (or to decide): Blodwen allowed ambiguities in the scrutinee
         -- to be delayed, but now I think it's better to have simpler
         -- resolution rules, and not delay

         est <- get EST
         fullImps <- getToBind fc (elabMode elabinfo)
                               (implicitMode elabinfo) env []
         log "elab.case" 5 $ "Doing a case under unbound implicits " ++ show fullImps

         scrn <- genVarName "scr"
         casen <- genCaseName !(prettyName !(toFullNames (Resolved (defining est))))

         -- Update environment so that linear bindings which were used
         -- (esp. in the scrutinee!) are set to 0 in the case type
         let env = updateMults (linearUsed est) env
         defs <- get Ctxt
         let vis = case !(lookupCtxtExact (Resolved (defining est)) (gamma defs)) of
                        Just gdef =>
                             if visibility gdef == Public
                                then Public
                                else Private
                        Nothing => Public

         -- if the scrutinee is ones of the arguments in 'env' we should
         -- split on that, rather than adding it as a new argument
         let splitOn = findScrutinee env scr

         caseretty_in <- case expected of
                           Just ty => getTerm ty
                           _ =>
                              do nmty <- genName "caseTy"
                                 metaVar fc erased env nmty (TType fc)

         (caseretty, _) <- bindImplicits fc (implicitMode elabinfo) defs env
                                         fullImps caseretty_in (TType fc)
         let casefnty
               = abstractFullEnvType fc (allow splitOn (explicitPi env))
                            (maybe (Bind fc scrn (Pi fc caseRig Explicit scrty)
                                       (weaken caseretty))
                                   (const caseretty) splitOn)
         (erasedargs, _) <- findErased casefnty

         logEnv "elab.case" 10 "Case env" env
         logTermNF "elab.case" 2 ("Case function type: " ++ show casen) [] casefnty
         traverse_ addToSave (keys (getMetas casefnty))

         -- If we've had to add implicits to the case type (because there
         -- were unbound implicits) then we're in a bit of a mess. Easiest
         -- way out is to throw an error and try again with the implicits
         -- actually bound! This is rather hacky, but a lot less fiddly than
         -- the alternative of fixing up the environment
         when (not (isNil fullImps)) $ findImpsIn fc [] [] casefnty
         cidx <- addDef casen (record { eraseArgs = erasedargs }
                                (newDef fc casen (if isErased rigc then erased else top)
                                      [] casefnty vis None))

         -- don't worry about totality of the case block; it'll be handled
         -- by the totality of the parent function
         setFlag fc (Resolved cidx) (SetTotal PartialOK)
         let caseRef : Term vars = Ref fc Func (Resolved cidx)

         let applyEnv = applyToFull fc caseRef env
         let appTm : Term vars
                   = maybe (App fc applyEnv scrtm)
                           (const applyEnv)
                           splitOn

         let alts' = map (updateClause casen splitOn nest env) alts
         log "elab.case" 2 $ "Nested: " ++ show (map getNestData (names nest))
         log "elab.case" 2 $ "Generated alts: " ++ show alts'
         logTermNF "elab.case" 2 "Case application" env appTm

         -- Start with empty nested names, since we've extended the rhs with
         -- ICaseLocal so they'll get rebuilt with the right environment
         let nest' = MkNested []
         ust <- get UST
         -- We don't want to keep rechecking delayed elaborators in the
         -- case block, because they're not going to make progress until
         -- we come out again, so save them
         let olddelayed = delayedElab ust
         put UST (record { delayedElab = [] } ust)
         processDecl [InCase] nest' [] (IDef fc casen alts')

         -- If there's no duplication of the scrutinee in the block,
         -- flag it as inlinable.
         -- This will be the case either if the scrutinee is a variable, in
         -- which case the duplication won't hurt, or if there's no variable
         -- duplicated in the body (what ghc calls W-safe)
         -- We'll check that second condition later, after generating the
         -- runtime (erased) case trees
         let inlineOK = maybe False (const True) splitOn
         when inlineOK $ setFlag fc casen Inline

         ust <- get UST
         put UST (record { delayedElab = olddelayed } ust)

         pure (appTm, gnf env caseretty)
  where
    mkLocalEnv : Env Term vs -> Env Term vs
    mkLocalEnv [] = []
    mkLocalEnv (b :: bs)
        = let b' = if isLinear (multiplicity b)
                      then setMultiplicity b erased
                      else b in
              b' :: mkLocalEnv bs

    -- Return the original name in the environment, and what it needs to be
    -- called in the case block. We need to mapping to build the ICaseLocal
    -- so that it applies to the right original variable
    getBindName : Int -> Name -> List Name -> (Name, Name)
    getBindName idx n@(UN un) vs
       = if n `elem` vs then (n, MN un idx) else (n, n)
    getBindName idx n vs
       = if n `elem` vs then (n, MN "_cn" idx) else (n, n)

    -- Returns a list of names that nestednames should be applied to, mapped
    -- to what the name has become in the case block, and a list of terms for
    -- the LHS of the case to be applied to.
    addEnv : {vs : _} ->
             Int -> Env Term vs -> List Name -> (List (Name, Name), List RawImp)
    addEnv idx [] used = ([], [])
    addEnv idx {vs = v :: vs} (b :: bs) used
        = let n = getBindName idx v used
              (ns, rest) = addEnv (idx + 1) bs (snd n :: used)
              ns' = n :: ns in
              (ns', IAs fc EmptyFC UseLeft (snd n) (Implicit fc True) :: rest)

    -- Replace a variable in the argument list; if the reference is to
    -- a variable kept in the outer environment (therefore not an argument
    -- in the list) don't consume it
    replace : (idx : Nat) -> RawImp -> List RawImp -> List RawImp
    replace Z lhs (old :: xs)
       = let lhs' = case old of
                         IAs loc' nameLoc' side n _ => IAs loc' nameLoc' side n lhs
                         _ => lhs in
             lhs' :: xs
    replace (S k) lhs (x :: xs)
        = x :: replace k lhs xs
    replace _ _ xs = xs

    mkSplit : Maybe (Var vs) ->
              RawImp -> List RawImp ->
              List RawImp
    mkSplit Nothing lhs args = reverse (lhs :: args)
    mkSplit (Just (MkVar {i} prf)) lhs args
        = reverse (replace i lhs args)

    -- Names used in the pattern we're matching on, so don't bind them
    -- in the generated case block
    usedIn : RawImp -> List Name
    usedIn (IBindVar _ n) = [UN n]
    usedIn (IApp _ f a) = usedIn f ++ usedIn a
    usedIn (IAs _ _ _ n a) = n :: usedIn a
    usedIn (IAlternative _ _ alts) = concatMap usedIn alts
    usedIn _ = []

    -- Get a name update for the LHS (so that if there's a nested data declaration
    -- the constructors are applied to the environment in the case block)
    nestLHS : FC -> (Name, (Maybe Name, List (Var vars), a)) -> (Name, RawImp)
    nestLHS fc (n, (mn, ns, t))
        = (n, apply (IVar fc (fromMaybe n mn))
                    (map (const (Implicit fc False)) ns))

    applyNested : NestedNames vars -> RawImp -> RawImp
    applyNested nest lhs
        = let fc = getFC lhs in
              substNames [] (map (nestLHS fc) (names nest)) lhs

    updateClause : Name -> Maybe (Var vars) ->
                   NestedNames vars ->
                   Env Term vars -> ImpClause -> ImpClause
    updateClause casen splitOn nest env (PatClause loc' lhs rhs)
        = let (ns, args) = addEnv 0 env (usedIn lhs)
              args' = mkSplit splitOn lhs args
              lhs' = apply (IVar loc' casen) args' in
              PatClause loc' (applyNested nest lhs')
                        (bindCaseLocals loc' (map getNestData (names nest))
                                        ns rhs)
    -- With isn't allowed in a case block but include for completeness
    updateClause casen splitOn nest env (WithClause loc' lhs wval prf flags cs)
        = let (_, args) = addEnv 0 env (usedIn lhs)
              args' = mkSplit splitOn lhs args
              lhs' = apply (IVar loc' casen) args' in
              WithClause loc' (applyNested nest lhs') wval prf flags cs
    updateClause casen splitOn nest env (ImpossibleClause loc' lhs)
        = let (_, args) = addEnv 0 env (usedIn lhs)
              args' = mkSplit splitOn lhs args
              lhs' = apply (IVar loc' casen) args' in
              ImpossibleClause loc' (applyNested nest lhs')


export
checkCase : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            RigCount -> ElabInfo ->
            NestedNames vars -> Env Term vars ->
            FC -> (scr : RawImp) -> (ty : RawImp) -> List ImpClause ->
            Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
checkCase rig elabinfo nest env fc scr scrty_in alts exp
    = delayElab fc rig env exp CaseBlock $
        do scrty_exp <- case scrty_in of
                             Implicit _ _ => guessScrType alts
                             _ => pure scrty_in
           (scrtyv, scrtyt) <- check erased elabinfo nest env scrty_exp
                                     (Just (gType fc))
           logTerm "elab.case" 10 "Expected scrutinee type" scrtyv
           -- Try checking at the given multiplicity; if that doesn't work,
           -- try checking at Rig1 (meaning that we're using a linear variable
           -- so the scrutinee should be linear)
           let chrig = if isErased rig then erased else top
           log "elab.case" 5 $ "Checking " ++ show scr ++ " at " ++ show chrig

           (scrtm_in, gscrty, caseRig) <- handle
              (do c <- runDelays (const True) $ check chrig elabinfo nest env scr (Just (gnf env scrtyv))
                  pure (fst c, snd c, chrig))
            $ \case
                e@(LinearMisuse _ _ r _)
                  => branchOne
                     (do c <- runDelays (const True) $ check linear elabinfo nest env scr
                              (Just (gnf env scrtyv))
                         pure (fst c, snd c, linear))
                     (throw e)
                     r
                e => throw e

           scrty <- getTerm gscrty
           logTermNF "elab.case" 5 "Scrutinee type" env scrty
           defs <- get Ctxt
           checkConcrete !(nf defs env scrty)
           caseBlock rig elabinfo fc nest env scr scrtm_in scrty caseRig alts exp
  where
    -- For the moment, throw an error if we haven't been able to work out
    -- the type of the case scrutinee, because we'll need it to build the
    -- type of the case block. But (TODO) consider delaying on failure?
    checkConcrete : NF vs -> Core ()
    checkConcrete (NApp _ (NMeta n i _) _)
        = throw (GenericMsg fc "Can't infer type for case scrutinee")
    checkConcrete _ = pure ()

    applyTo : Defs -> RawImp -> NF [] -> Core RawImp
    applyTo defs ty (NBind fc _ (Pi _ _ Explicit _) sc)
        = applyTo defs (IApp fc ty (Implicit fc False))
               !(sc defs (toClosure defaultOpts [] (Erased fc False)))
    applyTo defs ty (NBind _ x (Pi _ _ _ _) sc)
        = applyTo defs (INamedApp fc ty x (Implicit fc False))
               !(sc defs (toClosure defaultOpts [] (Erased fc False)))
    applyTo defs ty _ = pure ty

    -- Get the name and type of the family the scrutinee is in
    getRetTy : Defs -> NF [] -> Core (Maybe (Name, NF []))
    getRetTy defs (NBind fc _ (Pi _ _ _ _) sc)
        = getRetTy defs !(sc defs (toClosure defaultOpts [] (Erased fc False)))
    getRetTy defs (NTCon _ n _ arity _)
        = do Just ty <- lookupTyExact n (gamma defs)
                  | Nothing => pure Nothing
             pure (Just (n, !(nf defs [] ty)))
    getRetTy _ _ = pure Nothing

    -- Guess a scrutinee type by looking at the alternatives, so that we
    -- have a hint for building the case type
    guessScrType : List ImpClause -> Core RawImp
    guessScrType [] = pure $ Implicit fc False
    guessScrType (PatClause _ x _ :: xs)
        = case getFn x of
               IVar _ n =>
                  do defs <- get Ctxt
                     [(n', (_, ty))] <- lookupTyName n (gamma defs)
                         | _ => guessScrType xs
                     Just (tyn, tyty) <- getRetTy defs !(nf defs [] ty)
                         | _ => guessScrType xs
                     applyTo defs (IVar fc tyn) tyty
               _ => guessScrType xs
    guessScrType (_ :: xs) = guessScrType xs
