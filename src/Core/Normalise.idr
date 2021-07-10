module Core.Normalise

import Core.CaseTree
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Options
import Core.Primitives
import Core.TT
import Core.Value

import Libraries.Data.NameMap
import Libraries.Data.IntMap
import Data.List
import Data.Maybe
import Data.Nat
import Data.Vect

%default covering

-- A pair of a term and its normal form. This could be constructed either
-- from a term (via 'gnf') or a normal form (via 'glueBack') but the other
-- part will only be constructed when needed, because it's in Core.
public export
data Glued : List Name -> Type where
     MkGlue : (fromTerm : Bool) -> -- is it built from the term; i.e. can
                                   -- we read the term straight back?
              Core (Term vars) -> (Ref Ctxt Defs -> Core (NF vars)) -> Glued vars

export
isFromTerm : Glued vars -> Bool
isFromTerm (MkGlue ft _ _) = ft

export
getTerm : Glued vars -> Core (Term vars)
getTerm (MkGlue _ tm _) = tm

export
getNF : {auto c : Ref Ctxt Defs} -> Glued vars -> Core (NF vars)
getNF {c} (MkGlue _ _ nf) = nf c

Stack : List Name -> Type
Stack vars = List (FC, Closure vars)

evalWithOpts : {auto c : Ref Ctxt Defs} ->
               {free, vars : _} ->
               Defs -> EvalOpts ->
               Env Term free -> LocalEnv free vars ->
               Term (vars ++ free) -> Stack free -> Core (NF free)

export
evalClosure : {auto c : Ref Ctxt Defs} ->
              {free : _} -> Defs -> Closure free -> Core (NF free)

export
evalArg : {auto c : Ref Ctxt Defs} -> {free : _} -> Defs -> Closure free -> Core (NF free)
evalArg defs c = evalClosure defs c

export
toClosure : EvalOpts -> Env Term outer -> Term outer -> Closure outer
toClosure opts env tm = MkClosure opts [] env tm

updateLimit : NameType -> Name -> EvalOpts -> Core (Maybe EvalOpts)
updateLimit Func n opts
    = pure $ if isNil (reduceLimit opts)
         then Just opts
         else case lookup n (reduceLimit opts) of
                   Nothing => Nothing
                   Just Z => Nothing
                   Just (S k) =>
                      Just (record { reduceLimit $= set n k } opts)
  where
    set : Name -> Nat -> List (Name, Nat) -> List (Name, Nat)
    set n v [] = []
    set n v ((x, l) :: xs)
        = if x == n
             then (x, v) :: xs
             else (x, l) :: set n v xs
updateLimit t n opts = pure (Just opts)

data CaseResult a
     = Result a
     | NoMatch -- case alternative didn't match anything
     | GotStuck -- alternative matched, but got stuck later

parameters (defs : Defs, topopts : EvalOpts)
  mutual
    eval : {auto c : Ref Ctxt Defs} ->
           {free, vars : _} ->
           Env Term free -> LocalEnv free vars ->
           Term (vars ++ free) -> Stack free -> Core (NF free)
    eval env locs (Local fc mrig idx prf) stk
        = evalLocal env fc mrig idx prf stk locs
    eval env locs (Ref fc nt fn) stk
        = evalRef env False fc nt fn stk (NApp fc (NRef nt fn) stk)
    eval {vars} {free} env locs (Meta fc name idx args) stk
        = evalMeta env fc name idx (closeArgs args) stk
      where
        -- Yes, it's just a map, but specialising it by hand since we
        -- use this a *lot* and it saves the run time overhead of making
        -- a closure and calling APPLY.
        closeArgs : List (Term (vars ++ free)) -> List (Closure free)
        closeArgs [] = []
        closeArgs (t :: ts) = MkClosure topopts locs env t :: closeArgs ts
    eval env locs (Bind fc x (Lam _ r _ ty) scope) (thunk :: stk)
        = eval env (snd thunk :: locs) scope stk
    eval env locs (Bind fc x b@(Let _ r val ty) scope) stk
        = if (holesOnly topopts || argHolesOnly topopts) && not (tcInline topopts)
             then do b' <- traverse (\tm => eval env locs tm []) b
                     pure $ NBind fc x b'
                        (\defs', arg => evalWithOpts defs' topopts
                                                env (arg :: locs) scope stk)
             else eval env (MkClosure topopts locs env val :: locs) scope stk
    eval env locs (Bind fc x b scope) stk
        = do b' <- traverse (\tm => eval env locs tm []) b
             pure $ NBind fc x b'
                      (\defs', arg => evalWithOpts defs' topopts
                                              env (arg :: locs) scope stk)
    eval env locs (App fc fn arg) stk
        = case strategy topopts of
               CBV => do arg' <- eval env locs arg []
                         eval env locs fn ((fc, MkNFClosure topopts env arg') :: stk)
               CBN => eval env locs fn ((fc, MkClosure topopts locs env arg) :: stk)
    eval env locs (As fc s n tm) stk
        = if removeAs topopts
             then eval env locs tm stk
             else do n' <- eval env locs n stk
                     tm' <- eval env locs tm stk
                     pure (NAs fc s n' tm')
    eval env locs (TDelayed fc r ty) stk
        = do ty' <- eval env locs ty stk
             pure (NDelayed fc r ty')
    eval env locs (TDelay fc r ty tm) stk
        = pure (NDelay fc r (MkClosure topopts locs env ty)
                            (MkClosure topopts locs env tm))
    eval env locs (TForce fc r tm) stk
        = do tm' <- eval env locs tm []
             case tm' of
                  NDelay fc r _ arg =>
                      eval env (arg :: locs) (Local {name = UN "fvar"} fc Nothing _ First) stk
                  _ => pure (NForce fc r tm' stk)
    eval env locs (PrimVal fc c) stk = pure $ NPrimVal fc c
    eval env locs (Erased fc i) stk = pure $ NErased fc i
    eval env locs (TType fc) stk = pure $ NType fc

    -- Apply an evaluated argument (perhaps cached from an earlier evaluation)
    -- to a stack
    applyToStack : {auto c : Ref Ctxt Defs} ->
                   {free : _} ->
                   Env Term free -> Bool ->
                   NF free -> Stack free -> Core (NF free)
    applyToStack env cont (NBind fc _ (Lam _ _ _ _) sc) (arg :: stk)
        = do arg' <- sc defs $ snd arg
             applyToStack env cont arg' stk
    applyToStack env cont (NBind fc x b@(Let _ r val ty) sc) stk
        = if (holesOnly topopts || argHolesOnly topopts) && not (tcInline topopts)
             then do b' <- if cont
                              then traverse (\t => applyToStack env cont t []) b
                              else pure b
                     pure (NBind fc x b'
                              (\defs', arg => applyToStack env cont !(sc defs' arg) stk))
             else do val' <- applyToStack env cont val []
                     applyToStack env cont !(sc defs (MkNFClosure topopts env val')) stk
    applyToStack env cont (NBind fc x b sc) stk
        = do b' <- if cont
                      then traverse (\t => applyToStack env cont t []) b
                      else pure b
             pure (NBind fc x b'
                      (\defs', arg => applyToStack env cont !(sc defs' arg) stk))
    applyToStack env cont (NApp fc (NRef nt fn) args) stk
        = evalRef env False fc nt fn (args ++ stk)
                  (NApp fc (NRef nt fn) (args ++ stk))
    applyToStack env cont (NApp fc (NLocal mrig idx p) args) stk
        = evalLocal env fc mrig _ p (args ++ stk) []
    applyToStack env cont (NApp fc (NMeta n i args) args') stk
        = evalMeta env fc n i args (args' ++ stk)
    applyToStack env cont (NDCon fc n t a args) stk
        = pure $ NDCon fc n t a (args ++ stk)
    applyToStack env cont (NTCon fc n t a args) stk
        = pure $ NTCon fc n t a (args ++ stk)
    applyToStack env cont (NAs fc s p t) stk
       = if removeAs topopts
            then applyToStack env cont t stk
            else do p' <- applyToStack env cont p []
                    t' <- applyToStack env cont t stk
                    pure (NAs fc s p' t')
    applyToStack env cont (NDelayed fc r tm) stk
       = do tm' <- applyToStack env cont tm stk
            pure (NDelayed fc r tm')
    applyToStack env cont nf@(NDelay fc r ty tm) stk
       = pure nf -- stack should always be empty here!
    applyToStack env cont (NForce fc r tm args) stk
       = do tm' <- applyToStack env cont tm []
            case tm' of
                 NDelay fc r _ arg =>
                    eval env [arg] (Local {name = UN "fvar"} fc Nothing _ First) stk
                 _ => pure (NForce fc r tm' (args ++ stk))
    applyToStack env cont nf@(NPrimVal fc _) _ = pure nf
    applyToStack env cont nf@(NErased fc _) _ = pure nf
    applyToStack env cont nf@(NType fc) _ = pure nf

    evalLocClosure : {auto c : Ref Ctxt Defs} ->
                     {free : _} ->
                     Env Term free ->
                     FC -> Maybe Bool ->
                     Stack free ->
                     Closure free ->
                     Core (NF free)
    evalLocClosure env fc mrig stk (MkClosure opts locs' env' tm')
        = evalWithOpts defs opts env' locs' tm' stk
    evalLocClosure {free} env fc mrig stk (MkNFClosure opts env' nf)
        = applyToStack env' False nf stk

    evalLocal : {auto c : Ref Ctxt Defs} ->
                {free : _} ->
                Env Term free ->
                FC -> Maybe Bool ->
                (idx : Nat) -> (0 p : IsVar nm idx (vars ++ free)) ->
                Stack free ->
                LocalEnv free vars ->
                Core (NF free)
    -- If it's one of the free variables, we are done unless the free
    -- variable maps to a let-binding
    evalLocal env fc mrig idx prf stk []
        = if not (holesOnly topopts || argHolesOnly topopts)
             -- if we know it's not a let, no point in even running `getBinder`
             && fromMaybe True mrig
             then
               case getBinder prf env of
                    Let _ _ val _ => eval env [] val stk
                    _ => pure $ NApp fc (NLocal mrig idx prf) stk
             else pure $ NApp fc (NLocal mrig idx prf) stk
    evalLocal env fc mrig Z First stk (x :: locs)
        = evalLocClosure env fc mrig stk x
    evalLocal {vars = x :: xs} {free}
              env fc mrig (S idx) (Later p) stk (_ :: locs)
        = evalLocal {vars = xs} env fc mrig idx p stk locs

    updateLocal : EvalOpts -> Env Term free ->
                  (idx : Nat) -> (0 p : IsVar nm idx (vars ++ free)) ->
                  LocalEnv free vars -> NF free ->
                  LocalEnv free vars
    updateLocal opts env Z First (x :: locs) nf
        = MkNFClosure opts env nf :: locs
    updateLocal opts env (S idx) (Later p) (x :: locs) nf
        = x :: updateLocal opts env idx p locs nf
    updateLocal _ _ _ _ locs nf = locs

    evalMeta : {auto c : Ref Ctxt Defs} ->
               {free : _} ->
               Env Term free ->
               FC -> Name -> Int -> List (Closure free) ->
               Stack free -> Core (NF free)
    evalMeta env fc nm i args stk
        = let args' = if isNil stk then map (EmptyFC,) args
                         else map (EmptyFC,) args ++ stk
                        in
              evalRef env True fc Func (Resolved i) args'
                          (NApp fc (NMeta nm i args) stk)

    -- The commented out logging here might still be useful one day, but
    -- evalRef is used a lot and even these tiny checks turn out to be
    -- worth skipping if we can
    evalRef : {auto c : Ref Ctxt Defs} ->
              {free : _} ->
              Env Term free ->
              (isMeta : Bool) ->
              FC -> NameType -> Name -> Stack free -> (def : Lazy (NF free)) ->
              Core (NF free)
    evalRef env meta fc (DataCon tag arity) fn stk def
        = do -- logC "eval.ref.data" 50 $ do fn' <- toFullNames fn -- Can't use ! here, it gets lifted too far
             --                             pure $ "Found data constructor: " ++ show fn'
             pure $ NDCon fc fn tag arity stk
    evalRef env meta fc (TyCon tag arity) fn stk def
        = do -- logC "eval.ref.type" 50 $ do fn' <- toFullNames fn
             --                             pure $ "Found type constructor: " ++ show fn'
             pure $ ntCon fc fn tag arity stk
    evalRef env meta fc Bound fn stk def
        = do -- logC "eval.ref.bound" 50 $ do fn' <- toFullNames fn
             --                              pure $ "Found bound variable: " ++ show fn'
             pure def
    evalRef env meta fc nt@Func n stk def
        = do -- logC "eval.ref.func" 50 $ do n' <- toFullNames n
             --                             pure $ "Found function: " ++ show n'
             Just res <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure def
             let redok1 = evalAll topopts
             let redok2 = reducibleInAny (currentNS defs :: nestedNS defs)
                                         (fullname res)
                                         (visibility res)
             -- want to shortcut that second check, if we're evaluating
             -- everything, so don't let bind unless we need that log!
             let redok = redok1 || redok2
             checkTimer -- If we're going to time out anywhere, it'll be
                        -- when evaluating something recursive, so this is a
                        -- good place to check
             unless redok2 $ logC "eval.stuck" 5 $ do n' <- toFullNames n
                                                      pure $ "Stuck function: " ++ show n'
             if redok
                then do
                   Just opts' <- updateLimit nt n topopts
                        | Nothing => do log "eval.stuck" 10 $ "Function " ++ show n ++ " past reduction limit"
                                        pure def -- name is past reduction limit
                   evalDef env opts' meta fc
                           (multiplicity res) (definition res) (flags res) stk def
                else pure def

    getCaseBound : List (Closure free) ->
                   (args : List Name) ->
                   LocalEnv free more ->
                   Maybe (LocalEnv free (args ++ more))
    getCaseBound []            []        loc = Just loc
    getCaseBound []            (_ :: _)  loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) []        loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) (n :: ns) loc = (arg ::) <$> getCaseBound args ns loc

    evalConAlt : {auto c : Ref Ctxt Defs} ->
                 {more, free : _} ->
                 Env Term free ->
                 LocalEnv free more -> EvalOpts -> FC ->
                 Stack free ->
                 (args : List Name) ->
                 List (Closure free) ->
                 CaseTree (args ++ more) ->
                 Core (CaseResult (NF free))
    evalConAlt env loc opts fc stk args args' sc
         = do let Just bound = getCaseBound args' args loc
                   | Nothing => pure GotStuck
              evalTree env bound opts fc stk sc

    tryAlt : {auto c : Ref Ctxt Defs} ->
             {free, more : _} ->
             Env Term free ->
             LocalEnv free more -> EvalOpts -> FC ->
             Stack free -> NF free -> CaseAlt more ->
             Core (CaseResult (NF free))
    -- Ordinary constructor matching
    tryAlt {more} env loc opts fc stk (NDCon _ nm tag' arity args') (ConCase x tag args sc)
         = if tag == tag'
              then evalConAlt env loc opts fc stk args (map snd args') sc
              else pure NoMatch
    -- Type constructor matching, in typecase
    tryAlt {more} env loc opts fc stk (NTCon _ nm tag' arity args') (ConCase nm' tag args sc)
         = if nm == nm'
              then evalConAlt env loc opts fc stk args (map snd args') sc
              else pure NoMatch
    -- Primitive type matching, in typecase
    tryAlt env loc opts fc stk (NPrimVal _ c) (ConCase nm tag args sc)
         = case args of -- can't just test for it in the `if` for typing reasons
             [] => if UN (show c) == nm
                   then evalTree env loc opts fc stk sc
                   else pure NoMatch
             _ => pure NoMatch
    -- Type of type matching, in typecase
    tryAlt env loc opts fc stk (NType _) (ConCase (UN "Type") tag [] sc)
         = evalTree env loc opts fc stk sc
    -- Arrow matching, in typecase
    tryAlt {more}
           env loc opts fc stk (NBind pfc x (Pi fc' r e aty) scty) (ConCase (UN "->") tag [s,t] sc)
       = evalConAlt {more} env loc opts fc stk [s,t]
                  [MkNFClosure opts env aty,
                   MkNFClosure opts env (NBind pfc x (Lam fc' r e aty) scty)]
                  sc
    -- Delay matching
    tryAlt env loc opts fc stk (NDelay _ _ ty arg) (DelayCase tyn argn sc)
         = evalTree env (ty :: arg :: loc) opts fc stk sc
    -- Constant matching
    tryAlt env loc opts fc stk (NPrimVal _ c') (ConstCase c sc)
         = if c == c' then evalTree env loc opts fc stk sc
                      else pure NoMatch
    -- Default case matches against any *concrete* value
    tryAlt env loc opts fc stk val (DefaultCase sc)
         = if concrete val
              then evalTree env loc opts fc stk sc
              else pure GotStuck
      where
        concrete : NF free -> Bool
        concrete (NDCon _ _ _ _ _) = True
        concrete (NTCon _ _ _ _ _) = True
        concrete (NPrimVal _ _) = True
        concrete (NBind _ _ _ _) = True
        concrete (NType _) = True
        concrete _ = False
    tryAlt _ _ _ _ _ _ _ = pure GotStuck

    findAlt : {auto c : Ref Ctxt Defs} ->
              {args, free : _} ->
              Env Term free ->
              LocalEnv free args -> EvalOpts -> FC ->
              Stack free -> NF free -> List (CaseAlt args) ->
              Core (CaseResult (NF free))
    findAlt env loc opts fc stk val [] = do
      log "eval.casetree.stuck" 2 "Ran out of alternatives"
      pure GotStuck
    findAlt env loc opts fc stk val (x :: xs)
         = do Result val <- tryAlt env loc opts fc stk val x
                   | NoMatch => findAlt env loc opts fc stk val xs
                   | GotStuck => do
                       logC "eval.casetree.stuck" 5 $
                         pure $ "Got stuck matching " ++ show val ++ " against " ++ show !(toFullNames x)
                       pure GotStuck
              pure (Result val)

    evalTree : {auto c : Ref Ctxt Defs} ->
               {args, free : _} -> Env Term free -> LocalEnv free args ->
               EvalOpts -> FC ->
               Stack free -> CaseTree args ->
               Core (CaseResult (NF free))
    evalTree env loc opts fc stk (Case {name} idx x _ alts)
      = do xval <- evalLocal env fc Nothing idx (varExtend x) [] loc
           -- we have not defined quote yet (it depends on eval itself) so we show the NF
           -- i.e. only the top-level constructor.
           log "eval.casetree" 5 $ "Evaluated " ++ show name ++ " to " ++ show xval
           let loc' = updateLocal opts env idx (varExtend x) loc xval
           findAlt env loc' opts fc stk xval alts
    evalTree env loc opts fc stk (STerm _ tm)
          = case fuel opts of
                 Nothing => do res <- evalWithOpts defs opts env loc (embed tm) stk
                               pure (Result res)
                 Just Z => pure GotStuck
                 Just (S k) =>
                      do let opts' = record { fuel = Just k } opts
                         res <- evalWithOpts defs opts' env loc (embed tm) stk
                         pure (Result res)
    evalTree env loc opts fc stk _ = pure GotStuck

    -- Take arguments from the stack, as long as there's enough.
    -- Returns the arguments, and the rest of the stack
    takeFromStack : (arity : Nat) -> Stack free ->
                    Maybe (Vect arity (Closure free), Stack free)
    takeFromStack arity stk = takeStk arity stk []
      where
        takeStk : (remain : Nat) -> Stack free ->
                  Vect got (Closure free) ->
                  Maybe (Vect (got + remain) (Closure free), Stack free)
        takeStk {got} Z stk acc = Just (rewrite plusZeroRightNeutral got in
                                    reverse acc, stk)
        takeStk (S k) [] acc = Nothing
        takeStk {got} (S k) (arg :: stk) acc
           = rewrite sym (plusSuccRightSucc got k) in
                     takeStk k stk (snd arg :: acc)

    argsFromStack : (args : List Name) ->
                    Stack free ->
                    Maybe (LocalEnv free args, Stack free)
    argsFromStack [] stk = Just ([], stk)
    argsFromStack (n :: ns) [] = Nothing
    argsFromStack (n :: ns) (arg :: args)
         = do (loc', stk') <- argsFromStack ns args
              pure (snd arg :: loc', stk')

    evalOp : {auto c : Ref Ctxt Defs} ->
             {arity, free : _} ->
             (Vect arity (NF free) -> Maybe (NF free)) ->
             Stack free -> (def : Lazy (NF free)) ->
             Core (NF free)
    evalOp {arity} fn stk def
        = case takeFromStack arity stk of
               -- Stack must be exactly the right height
               Just (args, []) =>
                  do argsnf <- evalAll args
                     pure $ case fn argsnf of
                          Nothing => def
                          Just res => res
               _ => pure def
      where
        -- No traverse for Vect in Core...
        evalAll : Vect n (Closure free) -> Core (Vect n (NF free))
        evalAll [] = pure []
        evalAll (c :: cs) = pure $ !(evalClosure defs c) :: !(evalAll cs)

    evalDef : {auto c : Ref Ctxt Defs} ->
              {free : _} ->
              Env Term free -> EvalOpts ->
              (isMeta : Bool) -> FC ->
              RigCount -> Def -> List DefFlag ->
              Stack free -> (def : Lazy (NF free)) ->
              Core (NF free)
    evalDef env opts meta fc rigd (PMDef r args tree _ _) flags stk def
       -- If evaluating the definition fails (e.g. due to a case being
       -- stuck) return the default.
       -- We can use the definition if one of the following is true:
       --   + The 'alwayReduce' flag (r) is set
       --   + We're not in 'holesOnly', 'argHolesOnly' or 'tcInline'
       --         (that's the default mode)
       --   + It's a metavariable and not in Rig0
       --   + It's a metavariable and we're not in 'argHolesOnly'
       --   + It's inlinable and we're in 'tcInline'
        = if alwaysReduce r
             || (not (holesOnly opts || argHolesOnly opts || tcInline opts))
             || (meta && not (isErased rigd))
             || (meta && holesOnly opts)
             || (tcInline opts && elem TCInline flags)
             then case argsFromStack args stk of
                       Nothing => pure def
                       Just (locs', stk') =>
                            do Result res <- evalTree env locs' opts fc stk' tree
                                    | _ => pure def
                               pure res
             else pure def
    evalDef env opts meta fc rigd (Builtin op) flags stk def
        = evalOp (getOp op) stk def
    -- All other cases, use the default value, which is already applied to
    -- the stack
    evalDef env opts _ _ _ _ _ stk def = pure def

-- Make sure implicit argument order is right... 'vars' is used so we'll
-- write it explicitly, but it does appear after the parameters in 'eval'!
evalWithOpts {vars} defs opts = eval {vars} defs opts

evalClosure defs (MkClosure opts locs env tm)
    = eval defs opts env locs tm []
evalClosure defs (MkNFClosure opts env nf)
    = applyToStack defs opts env True nf []

export
evalClosureWithOpts : {auto c : Ref Ctxt Defs} ->
                      {free : _} ->
                      Defs -> EvalOpts -> Closure free -> Core (NF free)
evalClosureWithOpts defs opts (MkClosure _ locs env tm)
    = eval defs opts env locs tm []
evalClosureWithOpts defs opts (MkNFClosure _ env nf)
    = applyToStack defs opts env True nf []

export
nf : {auto c : Ref Ctxt Defs} ->
     {vars : _} ->
     Defs -> Env Term vars -> Term vars -> Core (NF vars)
nf defs env tm = eval defs defaultOpts env [] tm []

export
nfOpts : {auto c : Ref Ctxt Defs} ->
         {vars : _} ->
         EvalOpts -> Defs -> Env Term vars -> Term vars -> Core (NF vars)
nfOpts opts defs env tm = eval defs opts env [] tm []

export
gnf : {vars : _} ->
      Env Term vars -> Term vars -> Glued vars
gnf env tm
    = MkGlue True
             (pure tm)
             (\c => do defs <- get Ctxt
                       nf defs env tm)

export
gnfOpts : {vars : _} ->
          EvalOpts -> Env Term vars -> Term vars -> Glued vars
gnfOpts opts env tm
    = MkGlue True
             (pure tm)
             (\c => do defs <- get Ctxt
                       nfOpts opts defs env tm)

export
gType : FC -> Glued vars
gType fc = MkGlue True (pure (TType fc)) (const (pure (NType fc)))

export
gErased : FC -> Glued vars
gErased fc = MkGlue True (pure (Erased fc False)) (const (pure (NErased fc False)))

export
data QVar : Type where

public export
interface Quote tm where
    quote : {auto c : Ref Ctxt Defs} ->
            {vars : List Name} ->
            Defs -> Env Term vars -> tm vars -> Core (Term vars)
    quoteGen : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               Ref QVar Int -> Defs -> Env Term vars -> tm vars -> Core (Term vars)

    quote defs env tm
        = do q <- newRef QVar 0
             quoteGen q defs env tm

genName : {auto q : Ref QVar Int} -> String -> Core Name
genName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

mutual
  quoteArg : {auto c : Ref Ctxt Defs} ->
              {bound, free : _} ->
              Ref QVar Int -> Defs -> Bounds bound ->
              Env Term free -> Closure free ->
              Core (Term (bound ++ free))
  quoteArg q defs bounds env a
      = quoteGenNF q defs bounds env !(evalClosure defs a)


  quoteArgWithFC : {auto c : Ref Ctxt Defs} ->
                   {bound, free : _} ->
                   Ref QVar Int -> Defs -> Bounds bound ->
                   Env Term free -> (FC, Closure free) ->
                   Core ((FC, Term (bound ++ free)))
  quoteArgWithFC q defs bounds env
       = traversePair (quoteArg q defs bounds env)

  quoteArgs : {auto c : Ref Ctxt Defs} ->
              {bound, free : _} ->
              Ref QVar Int -> Defs -> Bounds bound ->
              Env Term free -> List (Closure free) ->
              Core (List (Term (bound ++ free)))
  quoteArgs q defs bounds env = traverse (quoteArg q defs bounds env)

  quoteArgsWithFC : {auto c : Ref Ctxt Defs} ->
                    {bound, free : _} ->
                    Ref QVar Int -> Defs -> Bounds bound ->
                    Env Term free -> List (FC, Closure free) ->
                    Core (List (FC, Term (bound ++ free)))
  quoteArgsWithFC q defs bounds env
      = traverse (quoteArgWithFC q defs bounds env)

  quoteHead : {auto c : Ref Ctxt Defs} ->
              {bound, free : _} ->
              Ref QVar Int -> Defs ->
              FC -> Bounds bound -> Env Term free -> NHead free ->
              Core (Term (bound ++ free))
  quoteHead {bound} q defs fc bounds env (NLocal mrig _ prf)
      = let MkVar prf' = addLater bound prf in
            pure $ Local fc mrig _ prf'
    where
      addLater : {idx : _} ->
                 (ys : List Name) -> (0 p : IsVar n idx xs) ->
                 Var (ys ++ xs)
      addLater [] isv = MkVar isv
      addLater (x :: xs) isv
          = let MkVar isv' = addLater xs isv in
                MkVar (Later isv')
  quoteHead q defs fc bounds env (NRef Bound (MN n i))
      = pure $ case findName bounds of
             Just (MkVar p) => Local fc Nothing _ (varExtend p)
             Nothing => Ref fc Bound (MN n i)
    where
      findName : Bounds bound' -> Maybe (Var bound')
      findName None = Nothing
      findName (Add x (MN n' i') ns)
          = if i == i' -- this uniquely identifies it, given how we
                       -- generated the names, and is a faster test!
               then Just (MkVar First)
               else do MkVar p <-findName ns
                       Just (MkVar (Later p))
      findName (Add x _ ns)
          = do MkVar p <-findName ns
               Just (MkVar (Later p))
  quoteHead q defs fc bounds env (NRef nt n) = pure $ Ref fc nt n
  quoteHead q defs fc bounds env (NMeta n i args)
      = do args' <- quoteArgs q defs bounds env args
           pure $ Meta fc n i args'

  quotePi : {auto c : Ref Ctxt Defs} ->
            {bound, free : _} ->
            Ref QVar Int -> Defs -> Bounds bound ->
            Env Term free -> PiInfo (NF free) ->
            Core (PiInfo (Term (bound ++ free)))
  quotePi q defs bounds env Explicit = pure Explicit
  quotePi q defs bounds env Implicit = pure Implicit
  quotePi q defs bounds env AutoImplicit = pure AutoImplicit
  quotePi q defs bounds env (DefImplicit t)
      = do t' <- quoteGenNF q defs bounds env t
           pure (DefImplicit t')

  quoteBinder : {auto c : Ref Ctxt Defs} ->
                {bound, free : _} ->
                Ref QVar Int -> Defs -> Bounds bound ->
                Env Term free -> Binder (NF free) ->
                Core (Binder (Term (bound ++ free)))
  quoteBinder q defs bounds env (Lam fc r p ty)
      = do ty' <- quoteGenNF q defs bounds env ty
           p' <- quotePi q defs bounds env p
           pure (Lam fc r p' ty')
  quoteBinder q defs bounds env (Let fc r val ty)
      = do val' <- quoteGenNF q defs bounds env val
           ty' <- quoteGenNF q defs bounds env ty
           pure (Let fc r val' ty')
  quoteBinder q defs bounds env (Pi fc r p ty)
      = do ty' <- quoteGenNF q defs bounds env ty
           p' <- quotePi q defs bounds env p
           pure (Pi fc r p' ty')
  quoteBinder q defs bounds env (PVar fc r p ty)
      = do ty' <- quoteGenNF q defs bounds env ty
           p' <- quotePi q defs bounds env p
           pure (PVar fc r p' ty')
  quoteBinder q defs bounds env (PLet fc r val ty)
      = do val' <- quoteGenNF q defs bounds env val
           ty' <- quoteGenNF q defs bounds env ty
           pure (PLet fc r val' ty')
  quoteBinder q defs bounds env (PVTy fc r ty)
      = do ty' <- quoteGenNF q defs bounds env ty
           pure (PVTy fc r ty')

  quoteGenNF : {auto c : Ref Ctxt Defs} ->
               {bound, vars : _} ->
               Ref QVar Int ->
               Defs -> Bounds bound ->
               Env Term vars -> NF vars -> Core (Term (bound ++ vars))
  quoteGenNF q defs bound env (NBind fc n b sc)
      = do var <- genName "qv"
           sc' <- quoteGenNF q defs (Add n var bound) env
                       !(sc defs (toClosure defaultOpts env (Ref fc Bound var)))
           b' <- quoteBinder q defs bound env b
           pure (Bind fc n b' sc')
  quoteGenNF q defs bound env (NApp fc f args)
      = do f' <- quoteHead q defs fc bound env f
           args' <- quoteArgsWithFC q defs bound env args
           pure $ applyWithFC f' args'
  quoteGenNF q defs bound env (NDCon fc n t ar args)
      = do args' <- quoteArgsWithFC q defs bound env args
           pure $ applyWithFC (Ref fc (DataCon t ar) n) args'
  quoteGenNF q defs bound env (NTCon fc n t ar args)
      = do args' <- quoteArgsWithFC q defs bound env args
           pure $ applyWithFC (Ref fc (TyCon t ar) n) args'
  quoteGenNF q defs bound env (NAs fc s n pat)
      = do n' <- quoteGenNF q defs bound env n
           pat' <- quoteGenNF q defs bound env pat
           pure (As fc s n' pat')
  quoteGenNF q defs bound env (NDelayed fc r arg)
      = do argQ <- quoteGenNF q defs bound env arg
           pure (TDelayed fc r argQ)
  quoteGenNF q defs bound env (NDelay fc r ty arg)
      = do argNF <- evalClosure defs (toHolesOnly arg)
           argQ <- quoteGenNF q defs bound env argNF
           tyNF <- evalClosure defs (toHolesOnly ty)
           tyQ <- quoteGenNF q defs bound env tyNF
           pure (TDelay fc r tyQ argQ)
    where
      toHolesOnly : Closure vs -> Closure vs
      toHolesOnly (MkClosure opts locs env tm)
          = MkClosure (record { holesOnly = True,
                                argHolesOnly = True } opts)
                      locs env tm
      toHolesOnly c = c
  quoteGenNF q defs bound env (NForce fc r arg args)
      = do args' <- quoteArgsWithFC q defs bound env args
           case arg of
                NDelay fc _ _ arg =>
                   do argNF <- evalClosure defs arg
                      pure $ applyWithFC !(quoteGenNF q defs bound env argNF) args'
                _ => do arg' <- quoteGenNF q defs bound env arg
                        pure $ applyWithFC (TForce fc r arg') args'
  quoteGenNF q defs bound env (NPrimVal fc c) = pure $ PrimVal fc c
  quoteGenNF q defs bound env (NErased fc i) = pure $ Erased fc i
  quoteGenNF q defs bound env (NType fc) = pure $ TType fc

export
Quote NF where
  quoteGen q defs env tm = quoteGenNF q defs None env tm

export
Quote Term where
  quoteGen q defs env tm = pure tm

export
Quote Closure where
  quoteGen q defs env c = quoteGen q defs env !(evalClosure defs c)

-- Resume a previously blocked normalisation with a new environment
export
continueNF : {auto c : Ref Ctxt Defs} ->
             {vars : _} ->
             Defs -> Env Term vars -> NF vars -> Core (NF vars)
continueNF defs env stuck
   = applyToStack defs defaultOpts env True stuck []

export
glueBack : {auto c : Ref Ctxt Defs} ->
           {vars : _} ->
           Defs -> Env Term vars -> NF vars -> Glued vars
glueBack defs env nf
    = MkGlue False
             (do empty <- clearDefs defs
                 quote empty env nf)
             (const (pure nf))

export
normalise : {auto c : Ref Ctxt Defs} ->
            {free : _} ->
            Defs -> Env Term free -> Term free -> Core (Term free)
normalise defs env tm = quote defs env !(nf defs env tm)

export
normaliseOpts : {auto c : Ref Ctxt Defs} ->
                {free : _} ->
                EvalOpts -> Defs -> Env Term free -> Term free -> Core (Term free)
normaliseOpts opts defs env tm
    = quote defs env !(nfOpts opts defs env tm)

export
normaliseHoles : {auto c : Ref Ctxt Defs} ->
                 {free : _} ->
                 Defs -> Env Term free -> Term free -> Core (Term free)
normaliseHoles defs env tm
    = quote defs env !(nfOpts withHoles defs env tm)

export
normaliseLHS : {auto c : Ref Ctxt Defs} ->
               {free : _} ->
               Defs -> Env Term free -> Term free -> Core (Term free)
normaliseLHS defs env (Bind fc n b sc)
    = pure $ Bind fc n b !(normaliseLHS defs (b :: env) sc)
normaliseLHS defs env tm
    = quote defs env !(nfOpts onLHS defs env tm)

export
normaliseArgHoles : {auto c : Ref Ctxt Defs} ->
                    {free : _} ->
                    Defs -> Env Term free -> Term free -> Core (Term free)
normaliseArgHoles defs env tm
    = quote defs env !(nfOpts withArgHoles defs env tm)

export
normaliseAll : {auto c : Ref Ctxt Defs} ->
               {free : _} ->
               Defs -> Env Term free -> Term free -> Core (Term free)
normaliseAll defs env tm
    = quote defs env !(nfOpts withAll defs env tm)

-- Normalise, but without normalising the types of binders. Dealing with
-- binders is the slow part of normalisation so whenever we can avoid it, it's
-- a big win
export
normaliseScope : {auto c : Ref Ctxt Defs} ->
                 {free : _} ->
                 Defs -> Env Term free -> Term free -> Core (Term free)
normaliseScope defs env (Bind fc n b sc)
    = pure $ Bind fc n b !(normaliseScope defs (b :: env) sc)
normaliseScope defs env tm = normalise defs env tm

export
etaContract : {auto _ : Ref Ctxt Defs} ->
              {vars : _} -> Term vars -> Core (Term vars)
etaContract tm = do
  defs <- get Ctxt
  logTerm "eval.eta" 5 "Attempting to eta contract subterms of" tm
  nf <- normalise defs (mkEnv EmptyFC _) tm
  logTerm "eval.eta" 5 "Evaluated to" nf
  res <- mapTermM act tm
  logTerm "eval.eta" 5 "Result of eta-contraction" res
  pure res

   where

    act : {vars : _} -> Term vars -> Core (Term vars)
    act tm = do
      logTerm "eval.eta" 10 "  Considering" tm
      case tm of
        (Bind _ x (Lam _ _ _ _) (App _ fn (Local _ _ Z _))) => do
          logTerm "eval.eta" 10 "  Shrinking candidate" fn
          let shrunk = shrinkTerm fn (DropCons SubRefl)
          case shrunk of
            Nothing => do
              log "eval.eta" 10 "  Failure!"
              pure tm
            Just tm' => do
              logTerm "eval.eta" 10 "  Success!" tm'
              pure tm'
        _ => pure tm

public export
interface Convert tm where
  convert : {auto c : Ref Ctxt Defs} ->
            {vars : List Name} ->
            Defs -> Env Term vars ->
            tm vars -> tm vars -> Core Bool
  convGen : {auto c : Ref Ctxt Defs} ->
            {vars : _} ->
            Ref QVar Int ->
            Defs -> Env Term vars ->
            tm vars -> tm vars -> Core Bool

  convert defs env tm tm'
      = do q <- newRef QVar 0
           convGen q defs env tm tm'

tryUpdate : {vars, vars' : _} ->
            List (Var vars, Var vars') ->
            Term vars -> Maybe (Term vars')
tryUpdate ms (Local fc l idx p)
    = do MkVar p' <- findIdx ms idx
         pure $ Local fc l _ p'
  where
    findIdx : List (Var vars, Var vars') -> Nat -> Maybe (Var vars')
    findIdx [] _ = Nothing
    findIdx ((MkVar {i} _, v) :: ps) n
        = if i == n then Just v else findIdx ps n
tryUpdate ms (Ref fc nt n) = pure $ Ref fc nt n
tryUpdate ms (Meta fc n i args) = pure $ Meta fc n i !(traverse (tryUpdate ms) args)
tryUpdate ms (Bind fc x b sc)
    = do b' <- tryUpdateB b
         pure $ Bind fc x b' !(tryUpdate (map weakenP ms) sc)
  where
    tryUpdatePi : PiInfo (Term vars) -> Maybe (PiInfo (Term vars'))
    tryUpdatePi Explicit = pure Explicit
    tryUpdatePi Implicit = pure Implicit
    tryUpdatePi AutoImplicit = pure AutoImplicit
    tryUpdatePi (DefImplicit t) = pure $ DefImplicit !(tryUpdate ms t)

    tryUpdateB : Binder (Term vars) -> Maybe (Binder (Term vars'))
    tryUpdateB (Lam fc r p t) = pure $ Lam fc r !(tryUpdatePi p) !(tryUpdate ms t)
    tryUpdateB (Let fc r v t) = pure $ Let fc r !(tryUpdate ms v) !(tryUpdate ms t)
    tryUpdateB (Pi fc r p t) = pure $ Pi fc r !(tryUpdatePi p) !(tryUpdate ms t)
    tryUpdateB _ = Nothing

    weakenP : {n : _} -> (Var vars, Var vars') ->
              (Var (n :: vars), Var (n :: vars'))
    weakenP (v, vs) = (weaken v, weaken vs)
tryUpdate ms (App fc f a) = pure $ App fc !(tryUpdate ms f) !(tryUpdate ms a)
tryUpdate ms (As fc s a p) = pure $ As fc s !(tryUpdate ms a) !(tryUpdate ms p)
tryUpdate ms (TDelayed fc r tm) = pure $ TDelayed fc r !(tryUpdate ms tm)
tryUpdate ms (TDelay fc r ty tm) = pure $ TDelay fc r !(tryUpdate ms ty) !(tryUpdate ms tm)
tryUpdate ms (TForce fc r tm) = pure $ TForce fc r !(tryUpdate ms tm)
tryUpdate ms (PrimVal fc c) = pure $ PrimVal fc c
tryUpdate ms (Erased fc i) = pure $ Erased fc i
tryUpdate ms (TType fc) = pure $ TType fc

mutual
  allConvNF : {auto c : Ref Ctxt Defs} ->
              {vars : _} ->
              Ref QVar Int -> Defs -> Env Term vars ->
              List (NF vars) -> List (NF vars) -> Core Bool
  allConvNF q defs env [] [] = pure True
  allConvNF q defs env (x :: xs) (y :: ys)
      = do ok <- allConvNF q defs env xs ys
           if ok then convGen q defs env x y
                 else pure False
  allConvNF q defs env _ _ = pure False

  -- return False if anything differs at the head, to quickly find
  -- conversion failures without going deeply into all the arguments.
  -- True means they might still match
  quickConv : List (NF vars) -> List (NF vars) -> Bool
  quickConv [] [] = True
  quickConv (x :: xs) (y :: ys) = quickConvArg x y && quickConv xs ys
    where
      quickConvHead : NHead vars -> NHead vars -> Bool
      quickConvHead (NLocal _ _ _) (NLocal _ _ _) = True
      quickConvHead (NRef _ n) (NRef _ n') = n == n'
      quickConvHead (NMeta n _ _) (NMeta n' _ _) = n == n'
      quickConvHead _ _ = False

      quickConvArg : NF vars -> NF vars -> Bool
      quickConvArg (NBind{}) _ = True -- let's not worry about eta here...
      quickConvArg _ (NBind{}) = True
      quickConvArg (NApp _ h _) (NApp _ h' _) = quickConvHead h h'
      quickConvArg (NDCon _ _ t _ _) (NDCon _ _ t' _ _) = t == t'
      quickConvArg (NTCon _ n _ _ _) (NTCon _ n' _ _ _) = n == n'
      quickConvArg (NAs _ _ _ t) (NAs _ _ _ t') = quickConvArg t t'
      quickConvArg (NDelayed _ _ t) (NDelayed _ _ t') = quickConvArg t t'
      quickConvArg (NDelay _ _ _ _) (NDelay _ _ _ _) = True
      quickConvArg (NForce _ _ t _) (NForce _ _ t' _) = quickConvArg t t'
      quickConvArg (NPrimVal _ c) (NPrimVal _ c') = c == c'
      quickConvArg (NType _) (NType _) = True
      quickConvArg (NErased _ _) _ = True
      quickConvArg _ (NErased _ _) = True
      quickConvArg _ _ = False
  quickConv _ _ = False

  allConv : {auto c : Ref Ctxt Defs} ->
            {vars : _} ->
            Ref QVar Int -> Defs -> Env Term vars ->
            List (Closure vars) -> List (Closure vars) -> Core Bool
  allConv q defs env xs ys
      = do xsnf <- traverse (evalClosure defs) xs
           ysnf <- traverse (evalClosure defs) ys
           if quickConv xsnf ysnf
              then allConvNF q defs env xsnf ysnf
              else pure False

  -- If the case trees match in structure, get the list of variables which
  -- have to match in the call
  getMatchingVarAlt : {auto c : Ref Ctxt Defs} ->
                      {args, args' : _} ->
                      Defs ->
                      List (Var args, Var args') ->
                      CaseAlt args -> CaseAlt args' ->
                      Core (Maybe (List (Var args, Var args')))
  getMatchingVarAlt defs ms (ConCase n tag cargs t) (ConCase n' tag' cargs' t')
      = if n == n'
           then do let Just ms' = extend cargs cargs' ms
                        | Nothing => pure Nothing
                   Just ms <- getMatchingVars defs ms' t t'
                        | Nothing => pure Nothing
                   -- drop the prefix from cargs/cargs' since they won't
                   -- be in the caller
                   pure (Just (mapMaybe (dropP cargs cargs') ms))
           else pure Nothing
    where
      weakenP : {c, c', args, args' : _} ->
                (Var args, Var args') ->
                (Var (c :: args), Var (c' :: args'))
      weakenP (v, vs) = (weaken v, weaken vs)

      extend : (cs : List Name) -> (cs' : List Name) ->
               (List (Var args, Var args')) ->
               Maybe (List (Var (cs ++ args), Var (cs' ++ args')))
      extend [] [] ms = pure ms
      extend (c :: cs) (c' :: cs') ms
          = do rest <- extend cs cs' ms
               pure ((MkVar First, MkVar First) :: map weakenP rest)
      extend _ _ _ = Nothing

      dropV : forall args .
              (cs : List Name) -> Var (cs ++ args) -> Maybe (Var args)
      dropV [] v = Just v
      dropV (c :: cs) (MkVar First) = Nothing
      dropV (c :: cs) (MkVar (Later x))
          = dropV cs (MkVar x)

      dropP : (cs : List Name) -> (cs' : List Name) ->
              (Var (cs ++ args), Var (cs' ++ args')) ->
              Maybe (Var args, Var args')
      dropP cs cs' (x, y) = pure (!(dropV cs x), !(dropV cs' y))

  getMatchingVarAlt defs ms (ConstCase c t) (ConstCase c' t')
      = if c == c'
           then getMatchingVars defs ms t t'
           else pure Nothing
  getMatchingVarAlt defs ms (DefaultCase t) (DefaultCase t')
      = getMatchingVars defs ms t t'
  getMatchingVarAlt defs _ _ _ = pure Nothing

  getMatchingVarAlts : {auto c : Ref Ctxt Defs} ->
                       {args, args' : _} ->
                       Defs ->
                       List (Var args, Var args') ->
                       List (CaseAlt args) -> List (CaseAlt args') ->
                       Core (Maybe (List (Var args, Var args')))
  getMatchingVarAlts defs ms [] [] = pure (Just ms)
  getMatchingVarAlts defs ms (a :: as) (a' :: as')
      = do Just ms <- getMatchingVarAlt defs ms a a'
                | Nothing => pure Nothing
           getMatchingVarAlts defs ms as as'
  getMatchingVarAlts defs _ _ _ = pure Nothing

  getMatchingVars : {auto c : Ref Ctxt Defs} ->
                    {args, args' : _} ->
                    Defs ->
                    List (Var args, Var args') ->
                    CaseTree args -> CaseTree args' ->
                    Core (Maybe (List (Var args, Var args')))
  getMatchingVars defs ms (Case _ p _ alts) (Case _ p' _ alts')
      = getMatchingVarAlts defs ((MkVar p, MkVar p') :: ms) alts alts'
  getMatchingVars defs ms (STerm i tm) (STerm i' tm')
      = do let Just tm'' = tryUpdate ms tm
               | Nothing => pure Nothing
           if !(convert defs (mkEnv (getLoc tm) args') tm'' tm')
              then pure (Just ms)
              else pure Nothing
  getMatchingVars defs ms (Unmatched _) (Unmatched _) = pure (Just ms)
  getMatchingVars defs ms Impossible Impossible = pure (Just ms)
  getMatchingVars _ _ _ _ = pure Nothing

  chkSameDefs : {auto c : Ref Ctxt Defs} ->
                {vars : _} ->
                Ref QVar Int -> Defs -> Env Term vars ->
                Name -> Name ->
                List (Closure vars) -> List (Closure vars) -> Core Bool
  chkSameDefs q defs env n n' nargs nargs'
     = do Just (PMDef _ args ct rt _) <- lookupDefExact n (gamma defs)
               | _ => pure False
          Just (PMDef _ args' ct' rt' _) <- lookupDefExact n' (gamma defs)
               | _ => pure False

          -- If the two case blocks match in structure, get which variables
          -- correspond. If corresponding variables convert, the two case
          -- blocks convert.
          Just ms <- getMatchingVars defs [] ct ct'
               | Nothing => pure False
          convertMatches ms
     where
       -- We've only got the index into the argument list, and the indices
       -- don't match up, which is annoying. But it'll always be there!
       getArgPos : Nat -> List (Closure vars) -> Maybe (Closure vars)
       getArgPos _ [] = Nothing
       getArgPos Z (c :: cs) = pure c
       getArgPos (S k) (c :: cs) = getArgPos k cs

       convertMatches : {vs, vs' : _} ->
                        List (Var vs, Var vs') ->
                        Core Bool
       convertMatches [] = pure True
       convertMatches ((MkVar {i} p, MkVar {i=i'} p') :: vs)
          = do let Just varg = getArgPos i nargs
                   | Nothing => pure False
               let Just varg' = getArgPos i' nargs'
                   | Nothing => pure False
               pure $ !(convGen q defs env varg varg') &&
                      !(convertMatches vs)

  -- If two names are standing for case blocks, check the blocks originate
  -- from the same place, and have the same scrutinee
  chkConvCaseBlock : {auto c : Ref Ctxt Defs} ->
                     {vars : _} ->
                     FC -> Ref QVar Int -> Defs -> Env Term vars ->
                     NHead vars -> List (Closure vars) ->
                     NHead vars -> List (Closure vars) -> Core Bool
  chkConvCaseBlock fc q defs env (NRef _ n) nargs (NRef _ n') nargs'
      = do NS _ (CaseBlock _ _) <- full (gamma defs) n
              | _ => pure False
           NS _ (CaseBlock _ _) <- full (gamma defs) n'
              | _ => pure False
           False <- chkSameDefs q defs env n n' nargs nargs'
              | True => pure True
           -- both case operators. Due to the way they're elaborated, two
           -- blocks might arise from the same source but have different
           -- names. So we consider them the same if the scrutinees convert,
           -- and the functions are defined at the same location. This is a
           -- bit of a hack - and relies on the location being stored in the
           -- term accurately - but otherwise it's a quick way to find out!
           Just def <- lookupCtxtExact n (gamma defs)
                | _ => pure False
           Just def' <- lookupCtxtExact n' (gamma defs)
                | _ => pure False
           let PMDef _ _ tree _ _ = definition def
                | _ => pure False
           let PMDef _ _ tree' _ _ = definition def'
                | _ => pure False
           let Just scpos = findArgPos tree
                | Nothing => pure False
           let Just scpos' = findArgPos tree'
                | Nothing => pure False
           let Just sc = getScrutinee scpos nargs
                | Nothing => pure False
           let Just sc' = getScrutinee scpos' nargs'
                | Nothing => pure False
           ignore $ convGen q defs env sc sc'
           pure (location def == location def')
    where
      -- Need to find the position of the scrutinee to see if they are the
      -- same
      findArgPos : CaseTree as -> Maybe Nat
      findArgPos (Case idx p _ _) = Just idx
      findArgPos _ = Nothing

      getScrutinee : Nat -> List (Closure vs) -> Maybe (Closure vs)
      getScrutinee Z (x :: xs) = Just x
      getScrutinee (S k) (x :: xs) = getScrutinee k xs
      getScrutinee _ _ = Nothing
  chkConvCaseBlock _ _ _ _ _ _ _ _ = pure False

  chkConvHead : {auto c : Ref Ctxt Defs} ->
                {vars : _} ->
                Ref QVar Int -> Defs -> Env Term vars ->
                NHead vars -> NHead vars -> Core Bool
  chkConvHead q defs env (NLocal _ idx _) (NLocal _ idx' _) = pure $ idx == idx'
  chkConvHead q defs env (NRef _ n) (NRef _ n') = pure $ n == n'
  chkConvHead q defs env (NMeta n i args) (NMeta n' i' args')
     = if i == i'
          then allConv q defs env args args'
          else pure False
  chkConvHead q defs env _ _ = pure False

  convBinders : {auto c : Ref Ctxt Defs} ->
                {vars : _} ->
                Ref QVar Int -> Defs -> Env Term vars ->
                Binder (NF vars) -> Binder (NF vars) -> Core Bool
  convBinders q defs env (Pi _ cx ix tx) (Pi _ cy iy ty)
      = if cx /= cy
           then pure False
           else convGen q defs env tx ty
  convBinders q defs env (Lam _ cx ix tx) (Lam _ cy iy ty)
      = if cx /= cy
           then pure False
           else convGen q defs env tx ty
  convBinders q defs env bx by
      = if multiplicity bx /= multiplicity by
           then pure False
           else convGen q defs env (binderType bx) (binderType by)


  export
  Convert NF where
    convGen q defs env (NBind fc x b sc) (NBind _ x' b' sc')
        = do var <- genName "conv"
             let c = MkClosure defaultOpts [] env (Ref fc Bound var)
             bok <- convBinders q defs env b b'
             if bok
                then do bsc <- sc defs c
                        bsc' <- sc' defs c
                        convGen q defs env bsc bsc'
                else pure False

    convGen q defs env tmx@(NBind fc x (Lam fc' c ix tx) scx) tmy
        = do empty <- clearDefs defs
             etay <- nf defs env
                        (Bind fc x (Lam fc' c !(traverse (quote empty env) ix) !(quote empty env tx))
                           (App fc (weaken !(quote empty env tmy))
                                (Local fc Nothing _ First)))
             convGen q defs env tmx etay
    convGen q defs env tmx tmy@(NBind fc y (Lam fc' c iy ty) scy)
        = do empty <- clearDefs defs
             etax <- nf defs env
                        (Bind fc y (Lam fc' c !(traverse (quote empty env) iy) !(quote empty env ty))
                           (App fc (weaken !(quote empty env tmx))
                                (Local fc Nothing _ First)))
             convGen q defs env etax tmy

    convGen q defs env (NApp fc val args) (NApp _ val' args')
        = if !(chkConvHead q defs env val val')
             then allConv q defs env args1 args2
             else chkConvCaseBlock fc q defs env val args1 val' args2
        where
          -- Discard file context information irrelevant for conversion checking
          args1 : List (Closure vars)
          args1 = map snd args

          args2 : List (Closure vars)
          args2 = map snd args'

    convGen q defs env (NDCon _ nm tag _ args) (NDCon _ nm' tag' _ args')
        = if tag == tag'
             then allConv q defs env (map snd args) (map snd args')
             else pure False
    convGen q defs env (NTCon _ nm tag _ args) (NTCon _ nm' tag' _ args')
        = if nm == nm'
             then allConv q defs env (map snd args) (map snd args')
             else pure False
    convGen q defs env (NAs _ _ _ tm) (NAs _ _ _ tm')
        = convGen q defs env tm tm'

    convGen q defs env (NDelayed _ r arg) (NDelayed _ r' arg')
        = if compatible r r'
             then convGen q defs env arg arg'
             else pure False
    convGen q defs env (NDelay _ r _ arg) (NDelay _ r' _ arg')
        = if compatible r r'
             then do -- if it's codata, don't reduce the argument or we might
                     -- go for ever, if it's infinite
                     adefs <- case r of
                                   LLazy => pure defs
                                   _ => clearDefs defs
                     convGen q adefs env arg arg'
             else pure False
    convGen q defs env (NForce _ r arg args) (NForce _ r' arg' args')
        = if compatible r r'
             then if !(convGen q defs env arg arg')
                     then allConv q defs env (map snd args) (map snd args')
                     else pure False
             else pure False

    convGen q defs env (NPrimVal _ c) (NPrimVal _ c') = pure (c == c')
    convGen q defs env (NErased _ _) _ = pure True
    convGen q defs env _ (NErased _ _) = pure True
    convGen q defs env (NType _) (NType _) = pure True
    convGen q defs env x y = pure False

  export
  Convert Term where
    convGen q defs env x y
        = convGen q defs env !(nf defs env x) !(nf defs env y)

  export
  Convert Closure where
    convGen q defs env x y
        = convGen q defs env !(evalClosure defs x) !(evalClosure defs y)

export
getValArity : Defs -> Env Term vars -> NF vars -> Core Nat
getValArity defs env (NBind fc x (Pi _ _ _ _) sc)
    = pure (S !(getValArity defs env !(sc defs (toClosure defaultOpts env (Erased fc False)))))
getValArity defs env val = pure 0

export
getArity : {auto c : Ref Ctxt Defs} ->
           {vars : _} ->
           Defs -> Env Term vars -> Term vars -> Core Nat
getArity defs env tm = getValArity defs env !(nf defs env tm)

-- Log message with a value, translating back to human readable names first
export
logNF : {vars : _} ->
        {auto c : Ref Ctxt Defs} ->
        (s : String) ->
        {auto 0 _ : KnownTopic s} ->
        Nat -> Lazy String -> Env Term vars -> NF vars -> Core ()
logNF str n msg env tmnf
    = when !(logging str n) $
        do defs <- get Ctxt
           tm <- quote defs env tmnf
           tm' <- toFullNames tm
           logString str n (msg ++ ": " ++ show tm')

-- Log message with a term, reducing holes and translating back to human
-- readable names first
export
logTermNF' : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             (s : String) ->
             {auto 0 _ : KnownTopic s} ->
             Nat -> Lazy String -> Env Term vars -> Term vars -> Core ()
logTermNF' str n msg env tm
    = do defs <- get Ctxt
         tmnf <- normaliseHoles defs env tm
         tm' <- toFullNames tmnf
         logString str n (msg ++ ": " ++ show tm')

export
logTermNF : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            (s : String) ->
            {auto 0 _ : KnownTopic s} ->
            Nat -> Lazy String -> Env Term vars -> Term vars -> Core ()
logTermNF str n msg env tm
    = when !(logging str n) $ logTermNF' str n msg env tm

export
logGlue : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          (s : String) ->
          {auto 0 _ : KnownTopic s} ->
          Nat -> Lazy String -> Env Term vars -> Glued vars -> Core ()
logGlue str n msg env gtm
    = when !(logging str n) $
        do defs <- get Ctxt
           tm <- getTerm gtm
           tm' <- toFullNames tm
           logString str n (msg ++ ": " ++ show tm')

export
logGlueNF : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            (s : String) ->
            {auto 0 _ : KnownTopic s} ->
            Nat -> Lazy String -> Env Term vars -> Glued vars -> Core ()
logGlueNF str n msg env gtm
    = when !(logging str n) $
        do defs <- get Ctxt
           tm <- getTerm gtm
           tmnf <- normaliseHoles defs env tm
           tm' <- toFullNames tmnf
           logString str n (msg ++ ": " ++ show tm')

export
logEnv : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         (s : String) ->
         {auto 0 _ : KnownTopic s} ->
         Nat -> String -> Env Term vars -> Core ()
logEnv str n msg env
    = when !(logging str n) $
        do logString str n msg
           dumpEnv env

  where

    dumpEnv : {vs : List Name} -> Env Term vs -> Core ()
    dumpEnv [] = pure ()
    dumpEnv {vs = x :: _} (Let _ c val ty :: bs)
        = do logTermNF' str n (msg ++ ": let " ++ show x) bs val
             logTermNF' str n (msg ++ ":" ++ show c ++ " " ++ show x) bs ty
             dumpEnv bs
    dumpEnv {vs = x :: _} (b :: bs)
        = do logTermNF' str n (msg ++ ":" ++ show (multiplicity b) ++ " " ++
                           show (piInfo b) ++ " " ++
                           show x) bs (binderType b)
             dumpEnv bs
replace' : {auto c : Ref Ctxt Defs} ->
           {vars : _} ->
           Int -> Defs -> Env Term vars ->
           (lhs : NF vars) -> (parg : Term vars) -> (exp : NF vars) ->
           Core (Term vars)
replace' {vars} tmpi defs env lhs parg tm
    = if !(convert defs env lhs tm)
         then pure parg
         else repSub tm
  where
    repArg : (Closure vars) -> Core (Term vars)
    repArg c
        = do tmnf <- evalClosure defs c
             replace' tmpi defs env lhs parg tmnf

    repSub : NF vars -> Core (Term vars)
    repSub (NBind fc x b scfn)
        = do b' <- traverse repSub b
             let x' = MN "tmp" tmpi
             sc' <- replace' (tmpi + 1) defs env lhs parg
                             !(scfn defs (toClosure defaultOpts env (Ref fc Bound x')))
             pure (Bind fc x b' (refsToLocals (Add x x' None) sc'))
    repSub (NApp fc hd [])
        = do empty <- clearDefs defs
             quote empty env (NApp fc hd [])
    repSub (NApp fc hd args)
        = do args' <- traverse (traversePair repArg) args
             pure $ applyWithFC
                        !(replace' tmpi defs env lhs parg (NApp fc hd []))
                        args'
    repSub (NDCon fc n t a args)
        = do args' <- traverse (traversePair repArg) args
             empty <- clearDefs defs
             pure $ applyWithFC
                        !(quote empty env (NDCon fc n t a []))
                        args'
    repSub (NTCon fc n t a args)
        = do args' <- traverse (traversePair repArg) args
             empty <- clearDefs defs
             pure $ applyWithFC
                        !(quote empty env (NTCon fc n t a []))
                        args'
    repSub (NAs fc s a p)
        = do a' <- repSub a
             p' <- repSub p
             pure (As fc s a' p')
    repSub (NDelayed fc r tm)
        = do tm' <- repSub tm
             pure (TDelayed fc r tm')
    repSub (NDelay fc r ty tm)
        = do ty' <- replace' tmpi defs env lhs parg !(evalClosure defs ty)
             tm' <- replace' tmpi defs env lhs parg !(evalClosure defs tm)
             pure (TDelay fc r ty' tm')
    repSub (NForce fc r tm args)
        = do args' <- traverse (traversePair repArg) args
             tm' <- repSub tm
             pure $ applyWithFC (TForce fc r tm') args'
    repSub tm = do empty <- clearDefs defs
                   quote empty env tm

export
replace : {auto c : Ref Ctxt Defs} ->
          {vars : _} ->
          Defs -> Env Term vars ->
          (orig : NF vars) -> (new : Term vars) -> (tm : NF vars) ->
          Core (Term vars)
replace = replace' 0

||| For printing purposes
export
normaliseErr : {auto c : Ref Ctxt Defs} ->
               Error -> Core Error
normaliseErr (CantConvert fc env l r)
    = do defs <- get Ctxt
         pure $ CantConvert fc env !(normaliseHoles defs env l >>= toFullNames)
                                   !(normaliseHoles defs env r >>= toFullNames)
normaliseErr (CantSolveEq fc env l r)
    = do defs <- get Ctxt
         pure $ CantSolveEq fc env !(normaliseHoles defs env l >>= toFullNames)
                                   !(normaliseHoles defs env r >>= toFullNames)
normaliseErr (WhenUnifying fc env l r err)
    = do defs <- get Ctxt
         pure $ WhenUnifying fc env !(normaliseHoles defs env l >>= toFullNames)
                                    !(normaliseHoles defs env r >>= toFullNames)
                                    !(normaliseErr err)
normaliseErr (CantSolveGoal fc env g)
    = do defs <- get Ctxt
         pure $ CantSolveGoal fc env !(normaliseHoles defs env g >>= toFullNames)
normaliseErr (AllFailed errs)
    = pure $ AllFailed !(traverse (\x => pure (fst x, !(normaliseErr (snd x)))) errs)
normaliseErr (InType fc n err)
    = pure $ InType fc n !(normaliseErr err)
normaliseErr (InCon fc n err)
    = pure $ InCon fc n !(normaliseErr err)
normaliseErr (InLHS fc n err)
    = pure $ InLHS fc n !(normaliseErr err)
normaliseErr (InRHS fc n err)
    = pure $ InRHS fc n !(normaliseErr err)
normaliseErr err = pure err


-- If the term is an application of a primitive conversion (fromInteger etc)
-- and it's applied to a constant, or is an application of a function
-- tagged as lhs pattern, fully normalise the term.
export
normalisePrimsOrPattern : {auto c : Ref Ctxt Defs} -> {vs : _} ->
                          -- size heuristic for when to unfold
                          (Constant -> Bool) ->
                          -- view to check whether an argument is a constant
                          (arg -> Maybe Constant) ->
                          -- Reduce everything (True) or just public export (False)
                          Bool ->
                          -- list of primitives
                          List Name ->
                          -- view of the potential redex
                          (n : Name) ->          -- function name
                          (args : List arg) ->   -- arguments from inside out (arg1, ..., argk)
                          -- actual term to evaluate if needed
                          (tm : Term vs) ->      -- original term (n arg1 ... argk)
                          Env Term vs ->         -- evaluation environment
                          -- output only evaluated if primitive
                          Core (Maybe (Term vs))
normalisePrimsOrPattern boundSafe viewConstant all prims n args tm env
   = do defs <- get Ctxt
        let norm = if all then normaliseAll else normalise
        let False = isJust $ lookup !(toResolvedNames n) defs.patternSynonyms
              | _ => Just <$> norm defs env tm -- is a LHS pattern
        let True = elem (dropNS !(getFullName n)) prims -- is a primitive
              | _ => pure Nothing
        let (mc :: _) = reverse args -- with at least one argument
              | _ => pure Nothing
        let (Just c) = viewConstant mc -- that is a constant
              | _ => pure Nothing
        let True = boundSafe c -- that we should expand
              | _ => pure Nothing
        Just <$> norm defs env tm
