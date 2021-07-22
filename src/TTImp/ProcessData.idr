module TTImp.ProcessData

import Core.CompileExpr
import Core.Context
import Core.Context.Data
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Hash
import Core.Metadata
import Core.Normalise
import Core.UnifyState
import Core.Value

import TTImp.BindImplicits
import TTImp.Elab.Check
import TTImp.Elab.Utils
import TTImp.Elab
import TTImp.TTImp
import TTImp.Utils

import Data.List
import Libraries.Data.NameMap

%default covering

processDataOpt : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> DataOpt -> Core ()
processDataOpt fc n NoHints
    = pure ()
processDataOpt fc ndef (SearchBy dets)
    = setDetermining fc ndef dets
processDataOpt fc ndef UniqueSearch
    = setUniqueSearch fc ndef True
processDataOpt fc ndef External
    = setExternal fc ndef True
processDataOpt fc ndef NoNewtype
    = pure ()

checkRetType : {auto c : Ref Ctxt Defs} ->
               Env Term vars -> NF vars ->
               (NF vars -> Core ()) -> Core ()
checkRetType env (NBind fc x (Pi _ _ _ ty) sc) chk
    = do defs <- get Ctxt
         checkRetType env !(sc defs (toClosure defaultOpts env (Erased fc False))) chk
checkRetType env nf chk = chk nf

checkIsType : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Env Term vars -> NF vars -> Core ()
checkIsType loc n env nf
    = checkRetType env nf $
         \case
           NType _ => pure ()
           _ => throw $ BadTypeConType loc n

checkFamily : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Name -> Env Term vars -> NF vars -> Core ()
checkFamily loc cn tn env nf
    = checkRetType env nf $
         \case
           NType _ => throw $ BadDataConType loc cn tn
           NTCon _ n' _ _ _ =>
                 if tn == n'
                    then pure ()
                    else throw $ BadDataConType loc cn tn
           _ => throw $ BadDataConType loc cn tn

updateNS : Name -> Name -> RawImp -> RawImp
updateNS orig ns (IPi fc c p n ty sc) = IPi fc c p n ty (updateNS orig ns sc)
updateNS orig ns tm = updateNSApp tm
  where
    updateNSApp : RawImp -> RawImp
    updateNSApp (IVar fc n) -- data type type, must be defined in this namespace
        = if n == orig
             then IVar fc ns
             else IVar fc n
    updateNSApp (IApp fc f arg) = IApp fc (updateNSApp f) arg
    updateNSApp (IAutoApp fc f arg) = IAutoApp fc (updateNSApp f) arg
    updateNSApp (INamedApp fc f n arg) = INamedApp fc (updateNSApp f) n arg
    updateNSApp t = t

checkCon : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           List ElabOpt -> NestedNames vars ->
           Env Term vars -> Visibility -> (orig : Name) -> (resolved : Name) ->
           ImpTy -> Core Constructor
checkCon {vars} opts nest env vis tn_in tn (MkImpTy fc _ cn_in ty_raw)
    = do cn <- inCurrentNS cn_in
         let ty_raw = updateNS tn_in tn ty_raw
         log "declare.data.constructor" 5 $ "Checking constructor type " ++ show cn ++ " : " ++ show ty_raw
         log "declare.data.constructor" 10 $ "Updated " ++ show (tn_in, tn)

         defs <- get Ctxt
         -- Check 'cn' is undefined
         Nothing <- lookupCtxtExact cn (gamma defs)
             | Just gdef => throw (AlreadyDefined fc cn)
         ty <-
             wrapErrorC opts (InCon fc cn) $
                   checkTerm !(resolveName cn) InType opts nest env
                              (IBindHere fc (PI erased) ty_raw)
                              (gType fc)

         -- Check 'ty' returns something in the right family
         checkFamily fc cn tn env !(nf defs env ty)
         let fullty = abstractEnvType fc env ty
         logTermNF "declare.data.constructor" 5 ("Constructor " ++ show cn) [] fullty

         traverse_ addToSave (keys (getMetas ty))
         addToSave cn
         log "declare.data.constructor" 10 $ "Saving from " ++ show cn ++ ": " ++ show (keys (getMetas ty))

         case vis of
              Public => do addHashWithNames cn
                           addHashWithNames fullty
              _ => pure ()
         pure (MkCon fc cn !(getArity defs [] fullty) fullty)

conName : Constructor -> Name
conName (MkCon _ cn _ _) = cn

-- Get the indices of the constructor type (with non-constructor parts erased)
getIndexPats : {auto c : Ref Ctxt Defs} ->
               ClosedTerm -> Core (List (NF []))
getIndexPats tm
    = do defs <- get Ctxt
         tmnf <- nf defs [] tm
         ret <- getRetType defs tmnf
         getPats defs ret
  where
    getRetType : Defs -> NF [] -> Core (NF [])
    getRetType defs (NBind fc _ (Pi _ _ _ _) sc)
        = do sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
             getRetType defs sc'
    getRetType defs t = pure t

    getPats : Defs -> NF [] -> Core (List (NF []))
    getPats defs (NTCon fc _ _ _ args)
        = traverse (evalClosure defs . snd) args
    getPats defs _ = pure [] -- Can't happen if we defined the type successfully!

getDetags : {auto c : Ref Ctxt Defs} ->
            FC -> List ClosedTerm -> Core (Maybe (List Nat))
getDetags fc [] = pure (Just []) -- empty type, trivially detaggable
getDetags fc [t] = pure (Just []) -- one constructor, trivially detaggable
getDetags fc tys
   = do ps <- traverse getIndexPats tys
        case !(getDisjointPos 0 (transpose ps)) of
             [] => pure $ Nothing
             xs => pure $ Just xs
  where
    mutual
      disjointArgs : List (NF []) -> List (NF []) -> Core Bool
      disjointArgs [] _ = pure False
      disjointArgs _ [] = pure False
      disjointArgs (a :: args) (a' :: args')
          = if !(disjoint a a')
               then pure True
               else disjointArgs args args'

      disjoint : NF [] -> NF [] -> Core Bool
      disjoint (NDCon _ _ t _ args) (NDCon _ _ t' _ args')
          = if t /= t'
               then pure True
               else do defs <- get Ctxt
                       argsnf <- traverse (evalClosure defs . snd) args
                       args'nf <- traverse (evalClosure defs . snd) args'
                       disjointArgs argsnf args'nf
      disjoint (NTCon _ n _ _ args) (NDCon _ n' _ _ args')
          = if n /= n'
               then pure True
               else do defs <- get Ctxt
                       argsnf <- traverse (evalClosure defs . snd) args
                       args'nf <- traverse (evalClosure defs . snd) args'
                       disjointArgs argsnf args'nf
      disjoint (NPrimVal _ c) (NPrimVal _ c') = pure (c /= c')
      disjoint _ _ = pure False

    allDisjointWith : NF [] -> List (NF []) -> Core Bool
    allDisjointWith val [] = pure True
    allDisjointWith (NErased _ _) _ = pure False
    allDisjointWith val (nf :: nfs)
        = do ok <- disjoint val nf
             if ok then allDisjointWith val nfs
                   else pure False

    allDisjoint : List (NF []) -> Core Bool
    allDisjoint [] = pure True
    allDisjoint (NErased _ _ :: _) = pure False
    allDisjoint (nf :: nfs)
        = do ok <- allDisjoint nfs
             if ok then allDisjointWith nf nfs
                   else pure False

    -- Which argument positions have completely disjoint contructors
    getDisjointPos : Nat -> List (List (NF [])) -> Core (List Nat)
    getDisjointPos i [] = pure []
    getDisjointPos i (args :: argss)
        = do rest <- getDisjointPos (1 + i) argss
             if !(allDisjoint args)
                then pure (i :: rest)
                else pure rest

-- If exactly one argument is unerased, return its position
getRelevantArg : Defs -> Nat -> Maybe Nat -> Bool -> NF [] ->
                 Core (Maybe (Bool, Nat))
getRelevantArg defs i rel world (NBind fc _ (Pi _ rig _ val) sc)
    = branchZero (getRelevantArg defs (1 + i) rel world
                              !(sc defs (toClosure defaultOpts [] (Erased fc False))))
                 (case val of
                       -- %World is never inspected, so might as well be deleted from data types,
                       -- although it needs care when compiling to ensure that the function that
                       -- returns the IO/%World type isn't erased
                       (NPrimVal _ WorldType) =>
                           getRelevantArg defs (1 + i) rel False
                               !(sc defs (toClosure defaultOpts [] (Erased fc False)))
                       _ =>
                       -- if we haven't found a relevant argument yet, make
                       -- a note of this one and keep going. Otherwise, we
                       -- have more than one, so give up.
                           maybe (do sc' <- sc defs (toClosure defaultOpts [] (Erased fc False))
                                     getRelevantArg defs (1 + i) (Just i) False sc')
                                 (const (pure Nothing))
                                 rel)
                 rig
getRelevantArg defs i rel world tm
    = pure (maybe Nothing (\r => Just (world, r)) rel)

-- If there's one constructor with only one non-erased argument, flag it as
-- a newtype for optimisation
export
findNewtype : {auto c : Ref Ctxt Defs} ->
              List Constructor -> Core ()
findNewtype [con]
    = do defs <- get Ctxt
         Just arg <- getRelevantArg defs 0 Nothing True !(nf defs [] (type con))
              | Nothing => pure ()
         updateDef (name con) $
               \case
                 DCon t a _ => Just $ DCon t a $ Just arg
                 _ => Nothing
findNewtype _ = pure ()

hasArgs : Nat -> Term vs -> Bool
hasArgs (S k) (Bind _ _ (Pi _ c _ _) sc)
    = if isErased c
         then hasArgs (S k) sc
         else hasArgs k sc
hasArgs (S k) _ = False
hasArgs Z (Bind _ _ (Pi _ c _ _) sc)
    = if isErased c
         then hasArgs Z sc
         else False
hasArgs Z _ = True

shaped : {auto c : Ref Ctxt Defs} ->
         (forall vs . Term vs -> Bool) ->
         List Constructor -> Core (Maybe Name)
shaped as [] = pure Nothing
shaped as (c :: cs)
    = do defs <- get Ctxt
         if as !(normalise defs [] (type c))
            then pure (Just (name c))
            else shaped as cs

-- Calculate whether the list of constructors gives a list-shaped type
-- If there's two constructors, one with no unerased arguments and one
-- with two unerased arguments, then it's listy.
-- If there's one constructor, with two unerased arugments, we can also
-- treat that as a cons cell, which will be cheaper for pairs.
-- Note they don't have to be recursive! It's just about whether we can
-- pair cheaply.
calcListy : {auto c : Ref Ctxt Defs} ->
            FC -> List Constructor -> Core Bool
calcListy fc cs@[_]
    = do Just cons <- shaped (hasArgs 2) cs
              | Nothing => pure False
         setFlag fc cons (ConType CONS)
         pure True
calcListy fc cs@[_, _]
    = do Just nil <- shaped (hasArgs 0) cs
              | Nothing => pure False
         Just cons <- shaped (hasArgs 2) cs
              | Nothing => pure False
         setFlag fc nil (ConType NIL)
         setFlag fc cons (ConType CONS)
         pure True
calcListy _ _ = pure False

-- It's option type shaped if there's two constructors, one of which has
-- zero arguments, and one of which has one.
calcMaybe : {auto c : Ref Ctxt Defs} ->
            FC -> List Constructor -> Core Bool
calcMaybe fc cs@[_, _]
    = do Just nothing <- shaped (hasArgs 0) cs
              | Nothing => pure False
         Just just <- shaped (hasArgs 1) cs
              | Nothing => pure False
         setFlag fc nothing (ConType NOTHING)
         setFlag fc just (ConType JUST)
         pure True
calcMaybe _ _ = pure False

calcEnum : {auto c : Ref Ctxt Defs} ->
           FC -> List Constructor -> Core Bool
calcEnum fc cs
    = if !(allM isNullary cs)
         then do traverse_ (\c => setFlag fc c (ConType ENUM)) (map name cs)
                 pure True
         else pure False
  where
    isNullary : Constructor -> Core Bool
    isNullary c
        = do defs <- get Ctxt
             pure $ hasArgs 0 !(normalise defs [] (type c))

calcRecord : {auto c : Ref Ctxt Defs} ->
             FC -> List Constructor -> Core Bool
calcRecord fc [c]
    = do setFlag fc (name c) (ConType RECORD)
         pure True
calcRecord _ _ = pure False

calcConInfo : {auto c : Ref Ctxt Defs} ->
              FC -> List Constructor -> Core ()
calcConInfo fc cons
   = do False <- calcListy fc cons
           | True => pure ()
        False <- calcMaybe fc cons
           | True => pure ()
        False <- calcEnum fc cons
           | True => pure ()
        False <- calcRecord fc cons
           | True => pure ()
        pure ()
     -- ... maybe more to come? The Bool just says when to stop looking

export
processData : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              List ElabOpt -> NestedNames vars ->
              Env Term vars -> FC -> Visibility ->
              ImpData -> Core ()
processData {vars} eopts nest env fc vis (MkImpLater dfc n_in ty_raw)
    = do n <- inCurrentNS n_in
         ty_raw <- bindTypeNames fc [] vars ty_raw

         defs <- get Ctxt
         -- Check 'n' is undefined
         Nothing <- lookupCtxtExact n (gamma defs)
             | Just gdef => throw (AlreadyDefined fc n)

         (ty, _) <-
             wrapErrorC eopts (InCon fc n) $
                    elabTerm !(resolveName n) InType eopts nest env
                              (IBindHere fc (PI erased) ty_raw)
                              (Just (gType dfc))
         let fullty = abstractEnvType dfc env ty
         logTermNF "declare.data" 5 ("data " ++ show n) [] fullty

         checkIsType fc n env !(nf defs env ty)
         arity <- getArity defs [] fullty

         -- Add the type constructor as a placeholder
         tidx <- addDef n (newDef fc n linear vars fullty vis
                          (TCon 0 arity [] [] defaultFlags [] [] Nothing))
         addMutData (Resolved tidx)
         defs <- get Ctxt
         traverse_ (\n => setMutWith fc n (mutData defs)) (mutData defs)

         traverse_ addToSave (keys (getMetas ty))
         addToSave n
         log "declare.data" 10 $ "Saving from " ++ show n ++ ": " ++ show (keys (getMetas ty))

         case vis of
              Private => pure ()
              _ => do addHashWithNames n
                      addHashWithNames fullty

processData {vars} eopts nest env fc vis (MkImpData dfc n_in ty_raw opts cons_raw)
    = do n <- inCurrentNS n_in
         ty_raw <- bindTypeNames fc [] vars ty_raw

         log "declare.data" 1 $ "Processing " ++ show n
         defs <- get Ctxt
         (ty, _) <-
             wrapErrorC eopts (InCon fc n) $
                    elabTerm !(resolveName n) InType eopts nest env
                              (IBindHere fc (PI erased) ty_raw)
                              (Just (gType dfc))
         let fullty = abstractEnvType dfc env ty

         -- If n exists, check it's the same type as we have here, and is
         -- a data constructor.
         -- When looking up, note the data types which were undefined at the
         -- point of declaration.
         ndefm <- lookupCtxtExact n (gamma defs)
         mw <- case ndefm of
                  Nothing => pure []
                  Just ndef =>
                    case definition ndef of
                         TCon _ _ _ _ _ mw [] _ =>
                            do ok <- convert defs [] fullty (type ndef)
                               if ok then pure mw
                                     else do logTermNF "declare.data" 1 "Previous" [] (type ndef)
                                             logTermNF "declare.data" 1 "Now" [] fullty
                                             throw (AlreadyDefined fc n)
                         _ => throw (AlreadyDefined fc n)

         logTermNF "declare.data" 5 ("data " ++ show n) [] fullty

         checkIsType fc n env !(nf defs env ty)
         arity <- getArity defs [] fullty

         -- Add the type constructor as a placeholder while checking
         -- data constructors
         tidx <- addDef n (newDef fc n linear vars fullty vis
                          (TCon 0 arity [] [] defaultFlags [] [] Nothing))
         case vis of
              Private => pure ()
              _ => do addHashWithNames n
                      addHashWithNames fullty

         -- Constructors are private if the data type as a whole is
         -- export
         let cvis = if vis == Export then Private else vis
         cons <- traverse (checkCon eopts nest env cvis n_in (Resolved tidx)) cons_raw

         let ddef = MkData (MkCon dfc n arity fullty) cons
         ignore $ addData vars vis tidx ddef

         -- Flag data type as a newtype, if possible (See `findNewtype` for criteria).
         -- Skip optimisation if the data type has specified `noNewtype` in its
         -- options list.
         when (not (NoNewtype `elem` opts)) $
              findNewtype cons

         -- Type is defined mutually with every data type undefined at the
         -- point it was declared, and every data type undefined right now
         defs <- get Ctxt
         let mutWith = nub (mw ++ mutData defs)
         log "declare.data" 3 $ show n ++ " defined in a mutual block with " ++ show mw
         setMutWith fc (Resolved tidx) mw

         traverse_ (processDataOpt fc (Resolved tidx)) opts
         dropMutData (Resolved tidx)

         detags <- getDetags fc (map type cons)
         setDetags fc (Resolved tidx) detags

         traverse_ addToSave (keys (getMetas ty))
         addToSave n
         log "declare.data" 10 $ "Saving from " ++ show n ++ ": " ++ show (keys (getMetas ty))

         let connames = map conName cons
         unless (NoHints `elem` opts) $
              traverse_ (\x => addHintFor fc (Resolved tidx) x True False) connames

         calcConInfo fc cons
         traverse_ updateErasable (Resolved tidx :: connames)
