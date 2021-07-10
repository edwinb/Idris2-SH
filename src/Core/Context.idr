module Core.Context

import        Core.CaseTree
import        Core.CompileExpr
import public Core.Core
import        Core.Env
import        Core.Hash
import public Core.Name
import        Core.Options
import public Core.Options.Log
import public Core.TT

import Libraries.Utils.Binary

import Data.Fin
import Libraries.Data.IntMap
import Data.IOArray
import Data.List
import Data.List1
import Data.Maybe
import Data.Nat
import Libraries.Data.NameMap
import Libraries.Data.StringMap
import Libraries.Text.Distance.Levenshtein

import System
import System.Clock
import System.Directory

%default covering

public export
data HoleInfo
        = NotHole
        | SolvedHole Nat

public export
record PMDefInfo where
  constructor MkPMDefInfo
  holeInfo : HoleInfo -- data if it comes from a solved hole
  alwaysReduce : Bool -- always reduce, even when quoting etc
                 -- typically for inlinable metavariable solutions
  externalDecl : Bool -- declared in another module, which may affect how it
                      -- is compiled

export
defaultPI : PMDefInfo
defaultPI = MkPMDefInfo NotHole False False

public export
record TypeFlags where
  constructor MkTypeFlags
  uniqueAuto : Bool  -- should 'auto' implicits check for uniqueness
  external : Bool -- defined externally (e.g. in a C or Scheme library)

export
defaultFlags : TypeFlags
defaultFlags = MkTypeFlags False False

public export
record HoleFlags where
  constructor MkHoleFlags
  implbind : Bool -- stands for an implicitly bound name
  precisetype : Bool -- don't generalise multiplicities when instantiating

export
holeInit : Bool -> HoleFlags
holeInit b = MkHoleFlags b False

public export
data Def : Type where
    None : Def -- Not yet defined
    PMDef : (pminfo : PMDefInfo) ->
            (args : List Name) ->
            (treeCT : CaseTree args) ->
            (treeRT : CaseTree args) ->
            (pats : List (vs ** (Env Term vs, Term vs, Term vs))) ->
                -- original checked patterns (LHS/RHS) with the names in
                -- the environment. Used for display purposes, for helping
                -- find size changes in termination checking, and for
                -- generating specialised definitions (so needs to be the
                -- full, non-erased, term)
            Def -- Ordinary function definition
    ExternDef : (arity : Nat) -> Def
    ForeignDef : (arity : Nat) ->
                 List String -> -- supported calling conventions,
                                -- e.g "C:printf,libc,stdlib.h", "scheme:display", ...
                 Def
    Builtin : {arity : Nat} -> PrimFn arity -> Def
    DCon : (tag : Int) -> (arity : Nat) ->
           (newtypeArg : Maybe (Bool, Nat)) ->
               -- if only constructor, and only one argument is non-Rig0,
               -- flag it here. The Nat is the unerased argument position.
               -- The Bool is 'True' if there is no %World token in the
               -- structure, which means it is safe to completely erase
               -- when pattern matching (otherwise we still have to ensure
               -- that the value is inspected, to make sure external effects
               -- happen)
           Def -- data constructor
    TCon : (tag : Int) -> (arity : Nat) ->
           (parampos : List Nat) -> -- parameters
           (detpos : List Nat) -> -- determining arguments
           (flags : TypeFlags) -> -- should 'auto' implicits check
           (mutwith : List Name) ->
           (datacons : List Name) ->
           (detagabbleBy : Maybe (List Nat)) ->
                    -- argument positions which can be used for
                    -- detagging, if it's possible (to check if it's
                    -- safe to erase)
           Def
    Hole : (numlocs : Nat) -> -- Number of locals in scope at binding point
                              -- (mostly to help display)
           HoleFlags ->
           Def
    BySearch : RigCount -> (maxdepth : Nat) -> (defining : Name) -> Def
    -- Constraints are integer references into the current map of
    -- constraints in the UnifyState (see Core.UnifyState)
    Guess : (guess : ClosedTerm) ->
            (envbind : Nat) -> -- Number of things in the environment when
                               -- we guessed the term
            (constraints : List Int) -> Def
    ImpBind : Def -- global name temporarily standing for an implicitly bound name
    -- A delayed elaboration. The elaborators themselves are stored in the
    -- unification state
    Delayed : Def

export
Show Def where
  show None = "undefined"
  show (PMDef _ args ct rt pats)
      = show args ++ ";\nCompile time tree: " ++ show ct ++
        "\nRun time tree: " ++ show rt
  show (DCon t a nt)
      = "DataCon " ++ show t ++ " " ++ show a
           ++ maybe "" (\n => " (newtype by " ++ show n ++ ")") nt
  show (TCon t a ps ds u ms cons det)
      = "TyCon " ++ show t ++ " " ++ show a ++ " params: " ++ show ps ++
        " constructors: " ++ show cons ++
        " mutual with: " ++ show ms ++
        " detaggable by: " ++ show det
  show (ExternDef arity) = "<external def with arity " ++ show arity ++ ">"
  show (ForeignDef a cs) = "<foreign def with arity " ++ show a ++
                           " " ++ show cs ++">"
  show (Builtin {arity} _) = "<builtin with arith " ++ show arity ++ ">"
  show (Hole _ p) = "Hole" ++ if implbind p then " [impl]" else ""
  show (BySearch c depth def) = "Search in " ++ show def
  show (Guess tm _ cs) = "Guess " ++ show tm ++ " when " ++ show cs
  show ImpBind = "Bound name"
  show Delayed = "Delayed"

public export
record Constructor where
  constructor MkCon
  loc : FC
  name : Name
  arity : Nat
  type : ClosedTerm

public export
data DataDef : Type where
     MkData : (tycon : Constructor) -> (datacons : List Constructor) ->
              DataDef

public export
data Clause : Type where
     MkClause : {vars : _} ->
                (env : Env Term vars) ->
                (lhs : Term vars) -> (rhs : Term vars) -> Clause

export
Show Clause where
  show (MkClause {vars} env lhs rhs)
      = show vars ++ ": " ++ show lhs ++ " = " ++ show rhs

public export
data DefFlag
    = Inline
    | Invertible -- assume safe to cancel arguments in unification
    | Overloadable -- allow ad-hoc overloads
    | TCInline -- always inline before totality checking
         -- (in practice, this means it's reduced in 'normaliseHoles')
         -- This means the function gets inlined when calculating the size
         -- change graph, but otherwise not. It's only safe if the function
         -- being inlined is terminating no matter what, and is really a bit
         -- of a hack to make sure interface dictionaries are properly inlined
         -- (otherwise they look potentially non terminating) so use with
         -- care!
    | SetTotal TotalReq
    | BlockedHint -- a hint, but blocked for the moment (so don't use)
    | Macro
    | PartialEval (List (Name, Nat)) -- Partially evaluate on completing defintion.
         -- This means the definition is standing for a specialisation so we
         -- should evaluate the RHS, with reduction limits on the given names,
         -- and ensure the name has made progress in doing so (i.e. has reduced
         -- at least once)
    | AllGuarded -- safe to treat as a constructor for the purposes of
         -- productivity checking. All clauses are guarded by constructors,
         -- and there are no other function applications
    | ConType ConInfo
         -- Is it a special type of constructor, e.g. a nil or cons shaped
         -- thing, that can be compiled specially?

export
Eq DefFlag where
    (==) Inline Inline = True
    (==) Invertible Invertible = True
    (==) Overloadable Overloadable = True
    (==) TCInline TCInline = True
    (==) (SetTotal x) (SetTotal y) = x == y
    (==) BlockedHint BlockedHint = True
    (==) Macro Macro = True
    (==) (PartialEval x) (PartialEval y) = x == y
    (==) AllGuarded AllGuarded = True
    (==) (ConType x) (ConType y) = x == y
    (==) _ _ = False

export
Show DefFlag where
  show Inline = "inline"
  show Invertible = "invertible"
  show Overloadable = "overloadable"
  show TCInline = "tcinline"
  show (SetTotal x) = show x
  show BlockedHint = "blockedhint"
  show Macro = "macro"
  show (PartialEval _) = "partialeval"
  show AllGuarded = "allguarded"
  show (ConType ci) = "contype " ++ show ci

public export
data SizeChange = Smaller | Same | Unknown

export
Show SizeChange where
  show Smaller = "Smaller"
  show Same = "Same"
  show Unknown = "Unknown"

export
Eq SizeChange where
  Smaller == Smaller = True
  Same == Same = True
  Unknown == Unknown = True
  _ == _ = False

public export
record SCCall where
     constructor MkSCCall
     fnCall : Name -- Function called
     fnArgs : List (Maybe (Nat, SizeChange))
        -- relationship to arguments of calling function; argument position
        -- (in the calling function), and how its size changed in the call.
        -- 'Nothing' if it's not related to any of the calling function's
        -- arguments

export
Show SCCall where
  show c = show (fnCall c) ++ ": " ++ show (fnArgs c)

export
Eq SCCall where
  x == y = fnCall x == fnCall y && fnArgs x == fnArgs y

public export
record GlobalDef where
  constructor MkGlobalDef
  location : FC
  fullname : Name -- original unresolved name
  type : ClosedTerm
  eraseArgs : List Nat -- which argument positions to erase at runtime
  safeErase : List Nat -- which argument positions are safe to assume
                       -- erasable without 'dotting', because their types
                       -- are collapsible relative to non-erased arguments
  specArgs : List Nat -- arguments to specialise by
  inferrable : List Nat -- arguments which can be inferred from elsewhere in the type
  multiplicity : RigCount
  localVars : List Name -- environment name is defined in
  visibility : Visibility
  totality : Totality
  flags : List DefFlag
  refersToM : Maybe (NameMap Bool)
  refersToRuntimeM : Maybe (NameMap Bool)
  invertible : Bool -- for an ordinary definition, is it invertible in unification
  noCycles : Bool -- for metavariables, whether they can be cyclic (this
                  -- would only be allowed when using a metavariable as a
                  -- placeholder for a yet to be elaborated arguments, but
                  -- not for implicits because that'd indicate failing the
                  -- occurs check)
  linearChecked : Bool -- Flag whether we've already checked its linearity
  definition : Def
  compexpr : Maybe CDef
  namedcompexpr : Maybe NamedDef
  sizeChange : List SCCall

export
refersTo : GlobalDef -> NameMap Bool
refersTo def = maybe empty id (refersToM def)

export
refersToRuntime : GlobalDef -> NameMap Bool
refersToRuntime def = maybe empty id (refersToRuntimeM def)

export
findSetTotal : List DefFlag -> Maybe TotalReq
findSetTotal [] = Nothing
findSetTotal (SetTotal t :: _) = Just t
findSetTotal (_ :: xs) = findSetTotal xs

-- Label for array references
export
data Arr : Type where

-- A context entry. If it's never been looked up, we haven't decoded the
-- binary blob yet, so decode it first time
public export
data ContextEntry : Type where
     Coded : Namespace -> -- namespace for decoding into, with restoreNS
             Binary -> ContextEntry
     Decoded : GlobalDef -> ContextEntry

data PossibleName : Type where
     Direct : Name -> Int -> PossibleName -- full name and resolved name id
     Alias : Name -> -- aliased name (from "import as")
             Name -> Int -> -- real full name and resolved name, as above
             PossibleName

-- All the GlobalDefs. We can only have one context, because name references
-- point at locations in here, and if we have more than one the indices won't
-- match up. So, this isn't polymorphic.
export
record Context where
    constructor MkContext
    firstEntry : Int -- First entry in the current source file
    nextEntry : Int
    -- Map from full name to its position in the context
    resolvedAs : NameMap Int
    -- Map from strings to all the possible names in all namespaces
    possibles : StringMap (List PossibleName)
    -- Reference to the actual content, indexed by Int
    content : Ref Arr (IOArray ContextEntry)
    -- Branching depth, in a backtracking elaborator. 0 is top level; at lower
    -- levels we need to stage updates rather than add directly to the
    -- 'content' store
    branchDepth : Nat
    -- Things which we're going to add, if this branch succeeds
    staging : IntMap ContextEntry

    -- Namespaces which are visible (i.e. have been imported)
    -- This only matters during evaluation and type checking, to control
    -- access in a program - in all other cases, we'll assume everything is
    -- visible
    visibleNS : List Namespace
    allPublic : Bool -- treat everything as public. This is intended
                     -- for checking partially evaluated definitions
                     -- or for use outside of the main compilation
                     -- process (e.g. when implementing interactive
                     -- features such as case splitting).
    inlineOnly : Bool -- only return things with the 'alwaysReduce' flag
    hidden : NameMap () -- Never return these

export
getContent : Context -> Ref Arr (IOArray ContextEntry)
getContent = content

export
namesResolvedAs : Context -> NameMap Name
namesResolvedAs ctxt = map Resolved ctxt.resolvedAs

-- Implemented later, once we can convert to and from full names
-- Defined in Core.TTC
export
decode : Context -> Int -> (update : Bool) -> ContextEntry -> Core GlobalDef

initSize : Int
initSize = 10000

Grow : Int
Grow = initSize

export
initCtxtS : Int -> Core Context
initCtxtS s
    = do arr <- coreLift $ newArray s
         aref <- newRef Arr arr
         pure $ MkContext
            { firstEntry = 0
            , nextEntry = 0
            , resolvedAs = empty
            , possibles = empty
            , content = aref
            , branchDepth = 0
            , staging = empty
            , visibleNS = [partialEvalNS]
            , allPublic = False
            , inlineOnly = False
            , hidden = empty
            }

export
initCtxt : Core Context
initCtxt = initCtxtS initSize

addPossible : Name -> Int ->
              StringMap (List PossibleName) -> StringMap (List PossibleName)
addPossible n i ps
    = case userNameRoot n of
           Nothing => ps
           Just nr =>
              case lookup nr ps of
                   Nothing => insert nr [Direct n i] ps
                   Just nis => insert nr (Direct n i :: nis) ps

addAlias : Name -> Name -> Int ->
           StringMap (List PossibleName) -> StringMap (List PossibleName)
addAlias alias full i ps
    = case userNameRoot alias of
           Nothing => ps
           Just nr =>
              case lookup nr ps of
                   Nothing => insert nr [Alias alias full i] ps
                   Just nis => insert nr (Alias alias full i :: nis) ps

export
newEntry : Name -> Context -> Core (Int, Context)
newEntry n ctxt
    = do let idx = nextEntry ctxt
         let a = content ctxt
         arr <- get Arr
         when (idx >= max arr) $
                 do arr' <- coreLift $ newArrayCopy (max arr + Grow) arr
                    put Arr arr'
         pure (idx, record { nextEntry = idx + 1,
                             resolvedAs $= insert n idx,
                             possibles $= addPossible n idx
                           } ctxt)

-- Get the position of the next entry in the context array, growing the
-- array if it's out of bounds.
-- Updates the context with the mapping from name to index
export
getPosition : Name -> Context -> Core (Int, Context)
getPosition (Resolved idx) ctxt = pure (idx, ctxt)
getPosition n ctxt
    = case lookup n (resolvedAs ctxt) of
           Just idx =>
              do pure (idx, ctxt)
           Nothing => newEntry n ctxt

newAlias : Name -> Name -> Context -> Core Context
newAlias alias full ctxt
    = do (idx, ctxt) <- getPosition full ctxt
         pure $ record { possibles $= addAlias alias full idx } ctxt

export
getNameID : Name -> Context -> Maybe Int
getNameID (Resolved idx) ctxt = Just idx
getNameID n ctxt = lookup n (resolvedAs ctxt)

-- Add the name to the context, or update the existing entry if it's already
-- there.
-- If we're not at the top level, add it to the staging area
export
addCtxt : Name -> GlobalDef -> Context -> Core (Int, Context)
addCtxt n val ctxt_in
    = if branchDepth ctxt_in == 0
         then do (idx, ctxt) <- getPosition n ctxt_in
                 let a = content ctxt
                 arr <- get Arr
                 coreLift $ writeArray arr idx (Decoded val)
                 pure (idx, ctxt)
         else do (idx, ctxt) <- getPosition n ctxt_in
                 pure (idx, record { staging $= insert idx (Decoded val) } ctxt)

export
addEntry : Name -> ContextEntry -> Context -> Core (Int, Context)
addEntry n entry ctxt_in
    = if branchDepth ctxt_in == 0
         then do (idx, ctxt) <- getPosition n ctxt_in
                 let a = content ctxt
                 arr <- get Arr
                 coreLift $ writeArray arr idx entry
                 pure (idx, ctxt)
         else do (idx, ctxt) <- getPosition n ctxt_in
                 pure (idx, record { staging $= insert idx entry } ctxt)

returnDef : Bool -> Int -> GlobalDef -> Maybe (Int, GlobalDef)
returnDef False idx def = Just (idx, def)
returnDef True idx def
    = case definition def of
           PMDef pi _ _ _ _ =>
                 if alwaysReduce pi
                    then Just (idx, def)
                    else Nothing
           _ => Nothing

export
lookupCtxtExactI : Name -> Context -> Core (Maybe (Int, GlobalDef))
lookupCtxtExactI (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just val =>
                 pure $ returnDef (inlineOnly ctxt) idx !(decode ctxt idx True val)
           Nothing =>
              do arr <- get Arr @{content ctxt}
                 Just def <- coreLift (readArray arr idx)
                      | Nothing => pure Nothing
                 pure $ returnDef (inlineOnly ctxt) idx !(decode ctxt idx True def)
lookupCtxtExactI n ctxt
    = do let Just idx = lookup n (resolvedAs ctxt)
                  | Nothing => pure Nothing
         lookupCtxtExactI (Resolved idx) ctxt

export
lookupCtxtExact : Name -> Context -> Core (Maybe GlobalDef)
lookupCtxtExact (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just res =>
                do def <- decode ctxt idx True res
                   pure $ map (\(_, def) => def) $
                     returnDef (inlineOnly ctxt) idx def
           Nothing =>
              do arr <- get Arr @{content ctxt}
                 Just res <- coreLift (readArray arr idx)
                      | Nothing => pure Nothing
                 def <- decode ctxt idx True res
                 pure $ map (\(_, def) => def) $
                   returnDef (inlineOnly ctxt) idx def
lookupCtxtExact n ctxt
    = do Just (i, def) <- lookupCtxtExactI n ctxt
              | Nothing => pure Nothing
         pure (Just def)

export
lookupContextEntry : Name -> Context -> Core (Maybe (Int, ContextEntry))
lookupContextEntry (Resolved idx) ctxt
    = case lookup idx (staging ctxt) of
           Just res => pure (Just (idx, res))
           Nothing =>
              do let a = content ctxt
                 arr <- get Arr
                 Just res <- coreLift (readArray arr idx)
                      | Nothing => pure Nothing
                 pure (Just (idx, res))
lookupContextEntry n ctxt
    = do let Just idx = lookup n (resolvedAs ctxt)
                  | Nothing => pure Nothing
         lookupContextEntry (Resolved idx) ctxt

||| Check if the name has been hidden by the `%hide` directive.
export
isHidden : Name -> Context -> Bool
isHidden fulln ctxt = isJust $ lookup fulln (hidden ctxt)

export
lookupCtxtName : Name -> Context -> Core (List (Name, Int, GlobalDef))
lookupCtxtName n ctxt
    = case userNameRoot n of
           Nothing => do Just (i, res) <- lookupCtxtExactI n ctxt
                              | Nothing => pure []
                         pure [(n, i, res)]
           Just r =>
              do let Just ps = lookup r (possibles ctxt)
                      | Nothing => pure []
                 lookupPossibles [] ps
  where

    resn : (Name, Int, GlobalDef) -> Int
    resn (_, i, _) = i

    lookupPossibles : List (Name, Int, GlobalDef) -> -- accumulator
                      List PossibleName ->
                      Core (List (Name, Int, GlobalDef))
    lookupPossibles acc [] = pure (reverse acc)
    lookupPossibles acc (Direct fulln i :: ps)
       = case lookup fulln (hidden ctxt) of
              Nothing =>
                do Just res <- lookupCtxtExact (Resolved i) ctxt
                        | Nothing => lookupPossibles acc ps
                   if matches n fulln && not (i `elem` map resn acc)
                      then lookupPossibles ((fulln, i, res) :: acc) ps
                      else lookupPossibles acc ps
              _ => lookupPossibles acc ps
    lookupPossibles acc (Alias asn fulln i :: ps)
       = case lookup fulln (hidden ctxt) of
              Nothing =>
                do Just res <- lookupCtxtExact (Resolved i) ctxt
                        | Nothing => lookupPossibles acc ps
                   if (matches n asn) && not (i `elem` map resn acc)
                      then lookupPossibles ((fulln, i, res) :: acc) ps
                      else lookupPossibles acc ps
              _ => lookupPossibles acc ps

hideName : Name -> Context -> Context
hideName n ctxt = record { hidden $= insert n () } ctxt

branchCtxt : Context -> Core Context
branchCtxt ctxt = pure (record { branchDepth $= S } ctxt)

commitCtxt : Context -> Core Context
commitCtxt ctxt
    = case branchDepth ctxt of
           Z => pure ctxt
           S Z => -- add all the things from 'staging' to the real array
                  do let a = content ctxt
                     arr <- get Arr
                     coreLift $ commitStaged (toList (staging ctxt)) arr
                     pure (record { staging = empty,
                                    branchDepth = Z } ctxt)
           S k => pure (record { branchDepth = k } ctxt)
  where
    -- We know the array must be big enough, because it will have been resized
    -- if necessary in the branch to fit the index we've been given here
    commitStaged : List (Int, ContextEntry) -> IOArray ContextEntry -> IO ()
    commitStaged [] arr = pure ()
    commitStaged ((idx, val) :: rest) arr
        = do writeArray arr idx val
             commitStaged rest arr

export
newDef : FC -> Name -> RigCount -> List Name ->
         ClosedTerm -> Visibility -> Def -> GlobalDef
newDef fc n rig vars ty vis def
    = MkGlobalDef
        { location = fc
        , fullname = n
        , type = ty
        , eraseArgs = []
        , safeErase = []
        , specArgs = []
        , inferrable = []
        , multiplicity = rig
        , localVars = vars
        , visibility = vis
        , totality = unchecked
        , flags = []
        , refersToM = Nothing
        , refersToRuntimeM = Nothing
        , invertible = False
        , noCycles = False
        , linearChecked = False
        , definition = def
        , compexpr = Nothing
        , namedcompexpr = Nothing
        , sizeChange = []
        }

-- Rewrite rules, applied after type checking, for runtime code only
-- LHS and RHS must have the same type, but we don't (currently) require that
-- the result still type checks (which might happen e.g. if transforming to a
-- faster implementation with different behaviour)
-- (Q: Do we need the 'Env' here? Usually we end up needing an 'Env' with a
-- 'NF but we're working with terms rather than values...)
public export
data Transform : Type where
     MkTransform : {vars : _} ->
                   Name -> -- name for identifying the rule
                   Env Term vars -> Term vars -> Term vars -> Transform

||| Types that are transformed into a faster representation
||| during codegen.
public export
data BuiltinType : Type where
    BuiltinNatural : BuiltinType
    NaturalToInteger : BuiltinType
    IntegerToNatural : BuiltinType

export
Show BuiltinType where
    show BuiltinNatural = "Natural"
    show NaturalToInteger = "NaturalToInteger"
    show IntegerToNatural = "IntegerToNatural"

-- Token types to make it harder to get the constructor names
-- the wrong way round.
public export data ZERO = MkZERO
public export data SUCC = MkSUCC

||| Record containing names of 'Nat'-like constructors.
public export
record NatBuiltin where
    constructor MkNatBuiltin
    zero : Name
    succ : Name

||| Record containing information about a NatToInteger function.
public export
record NatToInt where
    constructor MkNatToInt
    natToIntArity : Nat -- total number of arguments
    natIdx : Fin natToIntArity -- index into arguments of the 'Nat'-like argument

||| Record containing information about a IntegerToNat function.
public export
record IntToNat where
    constructor MkIntToNat
    intToNatArity : Nat
    intIdx : Fin intToNatArity

||| Rewrite rules for %builtin pragmas
||| Seperate to 'Transform' because it must also modify case statements
||| behaviour should remain the same after this transform
public export
record BuiltinTransforms where
    constructor MkBuiltinTransforms
    natTyNames : NameMap NatBuiltin -- map from Nat-like names to their constructors
    natZNames : NameMap ZERO -- set of Z-like names
    natSNames : NameMap SUCC -- set of S-like names
    natToIntegerFns : NameMap NatToInt -- set of functions to transform to `id`
    integerToNatFns : NameMap IntToNat -- set of functions to transform to `max 0`

-- TODO: After next release remove nat from here and use %builtin pragma instead
initBuiltinTransforms : BuiltinTransforms
initBuiltinTransforms =
    let type = NS typesNS (UN "Nat")
        zero = NS typesNS (UN "Z")
        succ = NS typesNS (UN "S")
    in MkBuiltinTransforms
        { natTyNames = singleton type (MkNatBuiltin {zero, succ})
        , natZNames = singleton zero MkZERO
        , natSNames = singleton succ MkSUCC
        , natToIntegerFns = empty
        , integerToNatFns = empty
        }

export
getFnName : Transform -> Maybe Name
getFnName (MkTransform _ _ app _)
    = case getFn app of
           Ref _ _ fn => Just fn
           _ => Nothing

public export
interface HasNames a where
  full : Context -> a -> Core a
  resolved : Context -> a -> Core a

export
HasNames Name where
  full gam (Resolved i)
      = do Just gdef <- lookupCtxtExact (Resolved i) gam
                  -- May occasionally happen when working with metadata.
                  -- It's harmless, so just silently return the resolved name.
                | Nothing => pure (Resolved i)
           pure (fullname gdef)
  full gam n = pure n

  resolved gam (Resolved i)
      = pure (Resolved i)
  resolved gam n
      = do let Just i = getNameID n gam
                    | Nothing => pure n
           pure (Resolved i)

export
HasNames (Term vars) where
  full gam (Ref fc x (Resolved i))
      = do Just gdef <- lookupCtxtExact (Resolved i) gam
                | Nothing => pure (Ref fc x (Resolved i))
           pure (Ref fc x (fullname gdef))
  full gam (Meta fc x y xs)
      = pure (Meta fc x y !(traverse (full gam) xs))
  full gam (Bind fc x b scope)
      = pure (Bind fc x !(traverse (full gam) b) !(full gam scope))
  full gam (App fc fn arg)
      = pure (App fc !(full gam fn) !(full gam arg))
  full gam (As fc s p tm)
      = pure (As fc s !(full gam p) !(full gam tm))
  full gam (TDelayed fc x y)
      = pure (TDelayed fc x !(full gam y))
  full gam (TDelay fc x t y)
      = pure (TDelay fc x !(full gam t) !(full gam y))
  full gam (TForce fc r y)
      = pure (TForce fc r !(full gam y))
  full gam tm = pure tm

  resolved gam (Ref fc x n)
      = do let Just i = getNameID n gam
                | Nothing => pure (Ref fc x n)
           pure (Ref fc x (Resolved i))
  resolved gam (Meta fc x y xs)
      = do xs' <- traverse (resolved gam) xs
           let Just i = getNameID x gam
               | Nothing => pure (Meta fc x y xs')
           pure (Meta fc x i xs')
  resolved gam (Bind fc x b scope)
      = pure (Bind fc x !(traverse (resolved gam) b) !(resolved gam scope))
  resolved gam (App fc fn arg)
      = pure (App fc !(resolved gam fn) !(resolved gam arg))
  resolved gam (As fc s p tm)
      = pure (As fc s !(resolved gam p) !(resolved gam tm))
  resolved gam (TDelayed fc x y)
      = pure (TDelayed fc x !(resolved gam y))
  resolved gam (TDelay fc x t y)
      = pure (TDelay fc x !(resolved gam t) !(resolved gam y))
  resolved gam (TForce fc r y)
      = pure (TForce fc r !(resolved gam y))
  resolved gam tm = pure tm

export
HasNames Pat where
  full gam (PAs fc n p)
     = [| PAs (pure fc) (full gam n) (full gam p) |]
  full gam (PCon fc n i ar ps)
     = [| PCon (pure fc) (full gam n) (pure i) (pure ar) (traverse (full gam) ps) |]
  full gam (PTyCon fc n ar ps)
     = [| PTyCon (pure fc) (full gam n) (pure ar) (traverse (full gam) ps) |]
  full gam p@(PConst _ _) = pure p
  full gam (PArrow fc x p q)
     = [| PArrow (pure fc) (full gam x) (full gam p) (full gam q) |]
  full gam (PDelay fc laz p q)
     = [| PDelay (pure fc) (pure laz) (full gam p) (full gam q) |]
  full gam (PLoc fc n) = PLoc fc <$> full gam n
  full gam (PUnmatchable fc t) = PUnmatchable fc <$> full gam t

  resolved gam (PAs fc n p)
     = [| PAs (pure fc) (resolved gam n) (resolved gam p) |]
  resolved gam (PCon fc n i ar ps)
     = [| PCon (pure fc) (resolved gam n) (pure i) (pure ar) (traverse (resolved gam) ps) |]
  resolved gam (PTyCon fc n ar ps)
     = [| PTyCon (pure fc) (resolved gam n) (pure ar) (traverse (resolved gam) ps) |]
  resolved gam p@(PConst _ _) = pure p
  resolved gam (PArrow fc x p q)
     = [| PArrow (pure fc) (resolved gam x) (resolved gam p) (resolved gam q) |]
  resolved gam (PDelay fc laz p q)
     = [| PDelay (pure fc) (pure laz) (resolved gam p) (resolved gam q) |]
  resolved gam (PLoc fc n) = PLoc fc <$> resolved gam n
  resolved gam (PUnmatchable fc t) = PUnmatchable fc <$> resolved gam t

mutual
  export
  HasNames (CaseTree vars) where
    full gam (Case i v ty alts)
        = pure $ Case i v !(full gam ty) !(traverse (full gam) alts)
    full gam (STerm i tm)
        = pure $ STerm i !(full gam tm)
    full gam t = pure t

    resolved gam (Case i v ty alts)
        = pure $ Case i v !(resolved gam ty) !(traverse (resolved gam) alts)
    resolved gam (STerm i tm)
        = pure $ STerm i !(resolved gam tm)
    resolved gam t = pure t

  export
  HasNames (CaseAlt vars) where
    full gam (ConCase n t args sc)
        = do sc' <- full gam sc
             Just gdef <- lookupCtxtExact n gam
                | Nothing => pure (ConCase n t args sc')
             pure $ ConCase (fullname gdef) t args sc'
    full gam (DelayCase ty arg sc)
        = pure $ DelayCase ty arg !(full gam sc)
    full gam (ConstCase c sc)
        = pure $ ConstCase c !(full gam sc)
    full gam (DefaultCase sc)
        = pure $ DefaultCase !(full gam sc)

    resolved gam (ConCase n t args sc)
        = do sc' <- resolved gam sc
             let Just i = getNameID n gam
                | Nothing => pure (ConCase n t args sc')
             pure $ ConCase (Resolved i) t args sc'
    resolved gam (DelayCase ty arg sc)
        = pure $ DelayCase ty arg !(resolved gam sc)
    resolved gam (ConstCase c sc)
        = pure $ ConstCase c !(resolved gam sc)
    resolved gam (DefaultCase sc)
        = pure $ DefaultCase !(resolved gam sc)

export
HasNames (Env Term vars) where
  full gam [] = pure []
  full gam (b :: bs)
      = pure $ !(traverse (full gam) b) :: !(full gam bs)

  resolved gam [] = pure []
  resolved gam (b :: bs)
      = pure $ !(traverse (resolved gam) b) :: !(resolved gam bs)

export
HasNames Clause where
  full gam (MkClause env lhs rhs)
     = pure $ MkClause !(full gam env) !(full gam lhs) !(full gam rhs)

  resolved gam (MkClause env lhs rhs)
    = [| MkClause (resolved gam env) (resolved gam lhs) (resolved gam rhs) |]


export
HasNames Def where
  full gam (PMDef r args ct rt pats)
      = pure $ PMDef r args !(full gam ct) !(full gam rt)
                     !(traverse fullNamesPat pats)
    where
      fullNamesPat : (vs ** (Env Term vs, Term vs, Term vs)) ->
                     Core (vs ** (Env Term vs, Term vs, Term vs))
      fullNamesPat (_ ** (env, lhs, rhs))
          = pure $ (_ ** (!(full gam env),
                          !(full gam lhs), !(full gam rhs)))
  full gam (TCon t a ps ds u ms cs det)
      = pure $ TCon t a ps ds u !(traverse (full gam) ms)
                                !(traverse (full gam) cs) det
  full gam (BySearch c d def)
      = pure $ BySearch c d !(full gam def)
  full gam (Guess tm b cs)
      = pure $ Guess !(full gam tm) b cs
  full gam t = pure t

  resolved gam (PMDef r args ct rt pats)
      = pure $ PMDef r args !(resolved gam ct) !(resolved gam rt)
                     !(traverse resolvedNamesPat pats)
    where
      resolvedNamesPat : (vs ** (Env Term vs, Term vs, Term vs)) ->
                         Core (vs ** (Env Term vs, Term vs, Term vs))
      resolvedNamesPat (_ ** (env, lhs, rhs))
          = pure $ (_ ** (!(resolved gam env),
                          !(resolved gam lhs), !(resolved gam rhs)))
  resolved gam (TCon t a ps ds u ms cs det)
      = pure $ TCon t a ps ds u !(traverse (resolved gam) ms)
                                !(traverse (resolved gam) cs) det
  resolved gam (BySearch c d def)
      = pure $ BySearch c d !(resolved gam def)
  resolved gam (Guess tm b cs)
      = pure $ Guess !(resolved gam tm) b cs
  resolved gam t = pure t

export
StripNamespace Def where
  trimNS ns (PMDef i args ct rt pats)
      = PMDef i args (trimNS ns ct) rt (map trimNSpat pats)
    where
      trimNSpat : (vs ** (Env Term vs, Term vs, Term vs)) ->
                  (vs ** (Env Term vs, Term vs, Term vs))
      trimNSpat (vs ** (env, lhs, rhs))
          = (vs ** (env, trimNS ns lhs, trimNS ns rhs))
  trimNS ns d = d

  restoreNS ns (PMDef i args ct rt pats)
      = PMDef i args (restoreNS ns ct) rt (map restoreNSpat pats)
    where
      restoreNSpat : (vs ** (Env Term vs, Term vs, Term vs)) ->
                  (vs ** (Env Term vs, Term vs, Term vs))
      restoreNSpat (vs ** (env, lhs, rhs))
          = (vs ** (env, restoreNS ns lhs, restoreNS ns rhs))
  restoreNS ns d = d

export
StripNamespace GlobalDef where
  trimNS ns def = record { definition $= trimNS ns } def
  restoreNS ns def = record { definition $= restoreNS ns } def

HasNames (NameMap a) where
  full gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : NameMap a -> List (Name, a) -> Core (NameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (insert !(full gam k) v ms) ns

  resolved gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : NameMap a -> List (Name, a) -> Core (NameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (insert !(resolved gam k) v ms) ns

export
HasNames PartialReason where
  full gam NotStrictlyPositive = pure NotStrictlyPositive
  full gam (BadCall ns) = pure $ BadCall !(traverse (full gam) ns)
  full gam (RecPath ns) = pure $ RecPath !(traverse (full gam) ns)

  resolved gam NotStrictlyPositive = pure NotStrictlyPositive
  resolved gam (BadCall ns) = pure $ BadCall !(traverse (resolved gam) ns)
  resolved gam (RecPath ns) = pure $ RecPath !(traverse (resolved gam) ns)

export
HasNames Terminating where
  full gam (NotTerminating p) = pure $ NotTerminating !(full gam p)
  full gam t = pure t

  resolved gam (NotTerminating p) = pure $ NotTerminating !(resolved gam p)
  resolved gam t = pure t

export
HasNames Covering where
  full gam IsCovering = pure IsCovering
  full gam (MissingCases ts)
      = pure $ MissingCases !(traverse (full gam) ts)
  full gam (NonCoveringCall ns)
      = pure $ NonCoveringCall !(traverse (full gam) ns)

  resolved gam IsCovering = pure IsCovering
  resolved gam (MissingCases ts)
      = pure $ MissingCases !(traverse (resolved gam) ts)
  resolved gam (NonCoveringCall ns)
      = pure $ NonCoveringCall !(traverse (resolved gam) ns)

export
HasNames Totality where
  full gam (MkTotality t c) = pure $ MkTotality !(full gam t) !(full gam c)
  resolved gam (MkTotality t c) = pure $ MkTotality !(resolved gam t) !(resolved gam c)

export
HasNames SCCall where
  full gam sc = pure $ record { fnCall = !(full gam (fnCall sc)) } sc
  resolved gam sc = pure $ record { fnCall = !(resolved gam (fnCall sc)) } sc

export
HasNames a => HasNames (Maybe a) where
  full gam Nothing = pure Nothing
  full gam (Just x) = pure $ Just !(full gam x)
  resolved gam Nothing = pure Nothing
  resolved gam (Just x) = pure $ Just !(resolved gam x)

export
HasNames GlobalDef where
  full gam def
      = do
--            ts <- full gam (type def)
--            d <- full gam (definition def)
--            coreLift $ printLn (fullname def, ts)
--            coreLift $ printLn (fullname def, d)
           pure $ record { type = !(full gam (type def)),
                           definition = !(full gam (definition def)),
                           totality = !(full gam (totality def)),
                           refersToM = !(full gam (refersToM def)),
                           refersToRuntimeM = !(full gam (refersToRuntimeM def)),
                           sizeChange = !(traverse (full gam) (sizeChange def))
                         } def
  resolved gam def
      = pure $ record { type = !(resolved gam (type def)),
                        definition = !(resolved gam (definition def)),
                        totality = !(resolved gam (totality def)),
                        refersToM = !(resolved gam (refersToM def)),
                        refersToRuntimeM = !(resolved gam (refersToRuntimeM def)),
                        sizeChange = !(traverse (resolved gam) (sizeChange def))
                      } def

export
HasNames Transform where
  full gam (MkTransform n env lhs rhs)
      = pure $ MkTransform !(full gam n) !(full gam env)
                           !(full gam lhs) !(full gam rhs)

  resolved gam (MkTransform n env lhs rhs)
      = pure $ MkTransform !(resolved gam n) !(resolved gam env)
                           !(resolved gam lhs) !(resolved gam rhs)

-- Return all the currently defined names
export
allNames : Context -> Core (List Name)
allNames ctxt = traverse (full ctxt) $ map Resolved [1..nextEntry ctxt - 1]

public export
record Defs where
  constructor MkDefs
  gamma : Context
  mutData : List Name -- Currently declared but undefined data types
  currentNS : Namespace -- namespace for current definitions
  nestedNS : List Namespace -- other nested namespaces we can look in
  options : Options
  toSave : NameMap ()
  nextTag : Int
  typeHints : NameMap (List (Name, Bool))
     -- ^ a mapping from type names to hints (and a flag setting whether it's
     -- a "direct" hint). Direct hints are searched first (as part of a group)
     -- the indirect hints. Indirect hints, in practice, are used to find
     -- instances of parent interfaces, and we don't search these until we've
     -- tried to find a direct result via a constructor or a top level hint.
  autoHints : NameMap Bool
     -- ^ global search hints. A mapping from the hint name, to whether it is
     -- a "default hint". A default hint is used only if all other attempts
     -- to search fail (this flag is really only intended as a mechanism
     -- for defaulting of literals)
  openHints : NameMap ()
     -- ^ currently open global hints; just for the rest of this module (not exported)
     -- and prioritised
  localHints : NameMap ()
     -- ^ Hints defined in the current environment
  saveTypeHints : List (Name, Name, Bool)
     -- We don't look up anything in here, it's merely for saving out to TTC.
     -- We save the hints in the 'GlobalDef' itself for faster lookup.
  saveAutoHints : List (Name, Bool)
  transforms : NameMap (List Transform)
     -- ^ A mapping from names to transformation rules which update applications
     -- of that name
  saveTransforms : List (Name, Transform)
  builtinTransforms : BuiltinTransforms
     -- ^ A mapping from names to transformations resulting from a %builtin pragma
     -- seperate to `transforms` because these must always fire globally so run these
     -- when compiling to `CExp`.
  patternSynonyms : NameMap ()
  namedirectives : NameMap (List String)
  ifaceHash : Int
  importHashes : List (Namespace, Int)
     -- ^ interface hashes of imported modules
  imported : List (ModuleIdent, Bool, Namespace)
     -- ^ imported modules, whether to rexport, as namespace
  allImported : List (String, (ModuleIdent, Bool, Namespace))
     -- ^ all imported filenames/namespaces, just to avoid loading something
     -- twice unnecessarily (this is a record of all the things we've
     -- called 'readFromTTC' with, in practice)
  cgdirectives : List (CG, String)
     -- ^ Code generator directives, which are free form text and thus to
     -- be interpreted however the specific code generator requires
  toCompileCase : List Name
     -- ^ Names which need to be compiled to run time case trees
  incData : List (CG, String, List String)
     -- ^ What we've compiled incrementally for this module: codegen,
     -- object file, any additional CG dependent data (e.g. linker flags)
  allIncData : List (CG, List String, List String)
     -- ^ Incrementally compiled files for all imports. Only lists CGs for
     -- while all modules have associated incremental compile data
  toIR : NameMap ()
     -- ^ Names which need to be compiled to IR at the end of processing
     -- the current module
  userHoles : NameMap Bool
     -- ^ Metavariables the user still has to fill in. In practice, that's
     -- everything with a user accessible name and a definition of Hole.
     -- The Bool says whether it was introduced in another module.
  peFailures : NameMap ()
     -- ^ Partial evaluation names which have failed, so don't bother trying
     -- again
  timings : StringMap (Bool, Integer)
     -- ^ record of timings from logTimeRecord
  timer : Maybe (Integer, String)
     -- ^ for timing and checking timeouts; the maximum time after which a
     -- timeout should be thrown
  warnings : List Warning
     -- ^ as yet unreported warnings

-- Label for context references
export
data Ctxt : Type where


export
clearDefs : Defs -> Core Defs
clearDefs defs
    = pure (record { gamma->inlineOnly = True } defs)

export
initDefs : Core Defs
initDefs
    = do gam <- initCtxt
         pure $ MkDefs
           { gamma = gam
           , mutData = []
           , currentNS = mainNS
           , nestedNS = []
           , options = defaults
           , toSave = empty
           , nextTag = 100
           , typeHints = empty
           , autoHints = empty
           , openHints = empty
           , localHints = empty
           , saveTypeHints = []
           , saveAutoHints = []
           , transforms = empty
           , saveTransforms = []
           , builtinTransforms = initBuiltinTransforms
           , patternSynonyms = empty
           , namedirectives = empty
           , ifaceHash = 5381
           , importHashes = []
           , imported = []
           , allImported = []
           , cgdirectives = []
           , toCompileCase = []
           , incData = []
           , allIncData = []
           , toIR = empty
           , userHoles = empty
           , peFailures = empty
           , timings = empty
           , timer = Nothing
           , warnings = []
           }

-- Reset the context, except for the options
export
clearCtxt : {auto c : Ref Ctxt Defs} ->
            Core ()
clearCtxt
    = do defs <- get Ctxt
         put Ctxt (record { options = resetElab (options defs),
                            timings = timings defs } !initDefs)
  where
    resetElab : Options -> Options
    resetElab = record { elabDirectives = defaultElab }

export
getFieldNames : Context -> Namespace -> List Name
getFieldNames ctxt recNS
  = let nms = resolvedAs ctxt in
    keys $ flip filterBy nms $ \ n =>
      case isRF n of
        Nothing => False
        Just (ns, field) => ns == recNS

-- Find similar looking names in the context
export
getSimilarNames : {auto c : Ref Ctxt Defs} -> Name -> Core (List String)
getSimilarNames nm = case userNameRoot nm of
  Nothing => pure []
  Just str => if length str <= 1 then pure [] else
    let threshold : Nat := max 1 (assert_total (divNat (length str) 3))
        test : Name -> IO (Maybe Nat) := \ nm => do
            let (Just str') = userNameRoot nm
                   | _ => pure Nothing
            dist <- Levenshtein.compute str str'
            pure (dist <$ guard (dist <= threshold))
    in do defs <- get Ctxt
          kept <- coreLift $ mapMaybeM test (resolvedAs (gamma defs))
          let sorted = sortBy (\ x, y => compare (snd x) (snd y)) $ toList kept
          let roots = mapMaybe (showNames nm str . fst) sorted
          pure (nub roots)

  where

  showNames : Name -> String -> Name -> Maybe String
  showNames target str nm = do
    let root = nameRoot nm
    let True = str == root | _ => pure root
    let full = show nm
    let True = str == full || show target == full | _ => pure full
    Nothing


maybeMisspelling : {auto c : Ref Ctxt Defs} ->
                   Error -> Name -> Core a
maybeMisspelling err nm = do
  candidates <- getSimilarNames nm
  case candidates of
    [] => throw err
    (x::xs) => throw (MaybeMisspelling err (x ::: xs))

-- Throw an UndefinedName exception. But try to find similar names first.
export
undefinedName : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core a
undefinedName loc nm = maybeMisspelling (UndefinedName loc nm) nm

-- Throw a NoDeclaration exception. But try to find similar names first.
export
noDeclaration : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core a
noDeclaration loc nm = maybeMisspelling (NoDeclaration loc nm) nm

-- Get the canonical name of something that might have been aliased via
-- import as
export
canonicalName : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core Name
canonicalName fc n
    = do defs <- get Ctxt
         case !(lookupCtxtName n (gamma defs)) of
              [] => undefinedName fc n
              [(n, _, _)] => pure n
              ns => throw (AmbiguousName fc (map fst ns))

-- If the name is aliased, get the alias
export
aliasName : {auto c : Ref Ctxt Defs} ->
            Name -> Core Name
aliasName fulln
    = do defs <- get Ctxt
         let Just r = userNameRoot fulln
                | Nothing => pure fulln
         let Just ps = lookup r (possibles (gamma defs))
                | Nothing => pure fulln
         findAlias ps
  where
    findAlias : List PossibleName -> Core Name
    findAlias [] = pure fulln
    findAlias (Alias as full i :: ps)
        = if full == fulln
             then pure as
             else findAlias ps
    findAlias (_ :: ps) = findAlias ps

-- Beware: if your hashable thing contains (potentially resolved) names,
-- it'll be better to use addHashWithNames to make the hash independent
-- of the internal numbering of names.
export
addHash : {auto c : Ref Ctxt Defs} ->
          Hashable a => a -> Core ()
addHash x
    = do defs <- get Ctxt
         put Ctxt (record { ifaceHash = hashWithSalt (ifaceHash defs) x } defs)

export
initHash : {auto c : Ref Ctxt Defs} ->
           Core ()
initHash
    = do defs <- get Ctxt
         put Ctxt (record { ifaceHash = 5381 } defs)

export
addUserHole : {auto c : Ref Ctxt Defs} ->
              Bool -> -- defined in another module?
              Name -> -- hole name
              Core ()
addUserHole ext n
    = do defs <- get Ctxt
         put Ctxt (record { userHoles $= insert n ext } defs)

export
clearUserHole : {auto c : Ref Ctxt Defs} ->
                Name -> Core ()
clearUserHole n
    = do defs <- get Ctxt
         put Ctxt (record { userHoles $= delete n } defs)

export
getUserHoles : {auto c : Ref Ctxt Defs} ->
               Core (List Name)
getUserHoles
    = do defs <- get Ctxt
         let hs = sort (keys (userHoles defs))
         filterM (isHole defs) hs
  where
    -- If a hole is declared in one file and defined in another, its
    -- name won't have been cleared unless we've already looked up its
    -- definition (as addDef needs to be called to clear it). So here
    -- check that it's really a hole
    isHole : Defs -> Name -> Core Bool
    isHole defs n
        = do Just def <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure True
             pure $ case definition def of
                  None => True
                  Hole _ _ => True
                  _ => False

export
addDef : {auto c : Ref Ctxt Defs} ->
         Name -> GlobalDef -> Core Int
addDef n def
    = do defs <- get Ctxt
         (idx, gam') <- addCtxt n def (gamma defs)
         put Ctxt (record { gamma = gam' } defs)
         case definition def of
              None => pure ()
              Hole _ _ => pure ()
              _ => clearUserHole (fullname def)
         pure idx

export
addContextEntry : {auto c : Ref Ctxt Defs} ->
                  Namespace -> Name -> Binary -> Core Int
addContextEntry ns n def
    = do defs <- get Ctxt
         (idx, gam') <- addEntry n (Coded ns def) (gamma defs)
         put Ctxt (record { gamma = gam' } defs)
         pure idx

export
addContextAlias : {auto c : Ref Ctxt Defs} ->
                  Name -> Name -> Core ()
addContextAlias alias full
    = do defs <- get Ctxt
         Nothing <- lookupCtxtExact alias (gamma defs)
             | _ => pure () -- Don't add the alias if the name exists already
         gam' <- newAlias alias full (gamma defs)
         put Ctxt (record { gamma = gam' } defs)

export
addBuiltin : {arity : _} ->
             {auto x : Ref Ctxt Defs} ->
             Name -> ClosedTerm -> Totality ->
             PrimFn arity -> Core ()
addBuiltin n ty tot op
   = do ignore $
       addDef n $ MkGlobalDef
         { location = emptyFC
         , fullname = n
         , type = ty
         , eraseArgs = []
         , safeErase = []
         , specArgs = []
         , inferrable = []
         , multiplicity = top
         , localVars = []
         , visibility = Public
         , totality = tot
         , flags = [Inline]
         , refersToM = Nothing
         , refersToRuntimeM = Nothing
         , invertible = False
         , noCycles = False
         , linearChecked = True
         , definition = Builtin op
         , compexpr = Nothing
         , namedcompexpr = Nothing
         , sizeChange = []
         }

export
updateDef : {auto c : Ref Ctxt Defs} ->
            Name -> (Def -> Maybe Def) -> Core ()
updateDef n fdef
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
             | Nothing => pure ()
         case fdef (definition gdef) of
              Nothing => pure ()
              Just def' => ignore $ addDef n (record { definition = def' } gdef)

export
updateTy : {auto c : Ref Ctxt Defs} ->
           Int -> ClosedTerm -> Core ()
updateTy i ty
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
              | Nothing => pure ()
         ignore $ addDef (Resolved i) (record { type = ty } gdef)

export
setCompiled : {auto c : Ref Ctxt Defs} ->
              Name -> CDef -> Core ()
setCompiled n cexp
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure ()
         ignore $ addDef n (record { compexpr = Just cexp } gdef)

export
setNamedCompiled : {auto c : Ref Ctxt Defs} ->
                   Name -> NamedDef -> Core ()
setNamedCompiled n cexp
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure ()
         ignore $ addDef n (record { namedcompexpr = Just cexp } gdef)

-- Record that the name has been linearity checked so we don't need to do
-- it again
export
setLinearCheck : {auto c : Ref Ctxt Defs} ->
                 Int -> Bool -> Core ()
setLinearCheck i chk
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
              | Nothing => pure ()
         ignore $ addDef (Resolved i) (record { linearChecked = chk } gdef)

export
setCtxt : {auto c : Ref Ctxt Defs} -> Context -> Core ()
setCtxt gam
  = do defs <- get Ctxt
       put Ctxt (record { gamma = gam } defs)

export
resolveName : {auto c : Ref Ctxt Defs} ->
            Name -> Core Int
resolveName (Resolved idx) = pure idx
resolveName n
  = do defs <- get Ctxt
       (i, gam') <- getPosition n (gamma defs)
       setCtxt gam'
       pure i

export
addName : {auto c : Ref Ctxt Defs} ->
          Name -> Core Int
addName (Resolved idx) = pure idx
addName n
  = do defs <- get Ctxt
       (i, gam') <- newEntry n (gamma defs)
       setCtxt gam'
       pure i

-- Call this before trying alternative elaborations, so that updates to the
-- context are put in the staging area rather than writing over the mutable
-- array of definitions.
-- Returns the old context (the one we'll go back to if the branch fails)
export
branch : {auto c : Ref Ctxt Defs} ->
       Core Defs
branch
  = do ctxt <- get Ctxt
       gam' <- branchCtxt (gamma ctxt)
       setCtxt gam'
       pure ctxt

-- Call this after trying an elaboration to commit any changes to the mutable
-- array of definitions once we know they're correct. Only actually commits
-- when we're right back at the top level
export
commit : {auto c : Ref Ctxt Defs} ->
       Core ()
commit
  = do defs <- get Ctxt
       gam' <- commitCtxt (gamma defs)
       setCtxt gam'

export
depth : {auto c : Ref Ctxt Defs} ->
      Core Nat
depth
  = do defs <- get Ctxt
       pure (branchDepth (gamma defs))

export
dumpStaging : {auto c : Ref Ctxt Defs} ->
              Core ()
dumpStaging
    = do defs <- get Ctxt
         coreLift $ putStrLn $ "Staging area: " ++ show (keys (staging (gamma defs)))

-- Explicitly note that the name should be saved when writing out a .ttc
export
addToSave : {auto c : Ref Ctxt Defs} ->
          Name -> Core ()
addToSave n_in
  = do defs <- get Ctxt
       n <- full (gamma defs) n_in
       put Ctxt (record { toSave $= insert n (),
                          toIR $= insert n ()
                        } defs)

-- Specific lookup functions
export
lookupExactBy : (GlobalDef -> a) -> Name -> Context ->
              Core (Maybe a)
lookupExactBy fn n gam
  = do Just gdef <- lookupCtxtExact n gam
            | Nothing => pure Nothing
       pure (Just (fn gdef))

export
lookupNameBy : (GlobalDef -> a) -> Name -> Context ->
             Core (List (Name, Int, a))
lookupNameBy fn n gam
  = do gdef <- lookupCtxtName n gam
       pure (map (\ (n, i, gd) => (n, i, fn gd)) gdef)

export
lookupDefExact : Name -> Context -> Core (Maybe Def)
lookupDefExact = lookupExactBy definition

export
lookupDefName : Name -> Context -> Core (List (Name, Int, Def))
lookupDefName = lookupNameBy definition

export
lookupTyExact : Name -> Context -> Core (Maybe ClosedTerm)
lookupTyExact = lookupExactBy type

export
lookupTyName : Name -> Context -> Core (List (Name, Int, ClosedTerm))
lookupTyName = lookupNameBy type

export
lookupDefTyExact : Name -> Context -> Core (Maybe (Def, ClosedTerm))
lookupDefTyExact = lookupExactBy (\g => (definition g, type g))

-- private names are only visible in this namespace if their namespace
-- is the current namespace (or an outer one)
-- that is: the namespace of 'n' is a parent of nspace
export
visibleIn : Namespace -> Name -> Visibility -> Bool
visibleIn nspace (NS ns n) Private = isParentOf ns nspace
-- Public and Export names are always visible
visibleIn nspace n _ = True

export
visibleInAny : List Namespace -> Name -> Visibility -> Bool
visibleInAny nss n vis = any (\ns => visibleIn ns n vis) nss

reducibleIn : Namespace -> Name -> Visibility -> Bool
reducibleIn nspace (NS ns (UN n)) Export = isParentOf ns nspace
reducibleIn nspace (NS ns (UN n)) Private = isParentOf ns nspace
reducibleIn nspace (NS ns (RF n)) Export = isParentOf ns nspace
reducibleIn nspace (NS ns (RF n)) Private = isParentOf ns nspace
reducibleIn nspace n _ = True

export
reducibleInAny : List Namespace -> Name -> Visibility -> Bool
reducibleInAny nss n vis = any (\ns => reducibleIn ns n vis) nss

export
toFullNames : {auto c : Ref Ctxt Defs} ->
              HasNames a => a -> Core a
toFullNames t
    = do defs <- get Ctxt
         full (gamma defs) t

export
toResolvedNames : {auto c : Ref Ctxt Defs} ->
                  HasNames a => a -> Core a
toResolvedNames t
    = do defs <- get Ctxt
         resolved (gamma defs) t

-- Make the name look nicer for user display
export
prettyName : {auto c : Ref Ctxt Defs} ->
             Name -> Core String
prettyName (Nested (i, _) n)
    = do i' <- toFullNames (Resolved i)
         pure (!(prettyName i') ++ "," ++
               !(prettyName n))
prettyName (CaseBlock outer idx)
    = pure ("case block in " ++ outer)
prettyName (WithBlock outer idx)
    = pure ("with block in " ++ outer)
prettyName (NS ns n) = prettyName n
prettyName n = pure (show n)

-- Add a hash of a thing that contains names,
-- but convert the internal numbers to full names first.
-- This makes the hash not depend on the internal numbering,
-- which is unstable.
export
addHashWithNames : {auto c : Ref Ctxt Defs} ->
  Hashable a => HasNames a => a -> Core ()
addHashWithNames x = toFullNames x >>= addHash

export
setFlag : {auto c : Ref Ctxt Defs} ->
        FC -> Name -> DefFlag -> Core ()
setFlag fc n fl
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName fc n
         let flags' = fl :: filter (/= fl) (flags def)
         ignore $ addDef n (record { flags = flags' } def)

export
setNameFlag : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> DefFlag -> Core ()
setNameFlag fc n fl
    = do defs <- get Ctxt
         [(n', i, def)] <- lookupCtxtName n (gamma defs)
              | [] => undefinedName fc n
              | res => throw (AmbiguousName fc (map fst res))
         let flags' = fl :: filter (/= fl) (flags def)
         ignore $ addDef (Resolved i) (record { flags = flags' } def)

export
unsetFlag : {auto c : Ref Ctxt Defs} ->
            FC -> Name -> DefFlag -> Core ()
unsetFlag fc n fl
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName fc n
         let flags' = filter (/= fl) (flags def)
         ignore $ addDef n (record { flags = flags' } def)

export
hasFlag : {auto c : Ref Ctxt Defs} ->
          FC -> Name -> DefFlag -> Core Bool
hasFlag fc n fl
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName fc n
         pure (fl `elem` flags def)

export
setSizeChange : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> List SCCall -> Core ()
setSizeChange loc n sc
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         ignore $ addDef n (record { sizeChange = sc } def)

export
setTotality : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Totality -> Core ()
setTotality loc n tot
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         ignore $ addDef n (record { totality = tot } def)

export
setCovering : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Covering -> Core ()
setCovering loc n tot
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         ignore $ addDef n (record { totality->isCovering = tot } def)

export
setTerminating : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Terminating -> Core ()
setTerminating loc n tot
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         ignore $ addDef n (record { totality->isTerminating = tot } def)

export
getTotality : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Core Totality
getTotality loc n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         pure $ totality def

export
getSizeChange : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core (List SCCall)
getSizeChange loc n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         pure $ sizeChange def

export
setVisibility : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Visibility -> Core ()
setVisibility fc n vis
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName fc n
         ignore $ addDef n (record { visibility = vis } def)

-- Set a name as Private that was previously visible (and, if 'everywhere' is
-- set, hide in any modules imported by this one)
export
hide : {auto c : Ref Ctxt Defs} ->
       FC -> Name -> Core ()
hide fc n
    = do defs <- get Ctxt
         [(nsn, _)] <- lookupCtxtName n (gamma defs)
              | [] => undefinedName fc n
              | res => throw (AmbiguousName fc (map fst res))
         put Ctxt (record { gamma $= hideName nsn } defs)

export
getVisibility : {auto c : Ref Ctxt Defs} ->
                FC -> Name -> Core Visibility
getVisibility fc n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName fc n
         pure $ visibility def

public export
record SearchData where
  constructor MkSearchData
  detArgs : List Nat -- determining argument positions
  hintGroups : List (Bool, List Name)
       -- names of functions to use as hints, and whether ambiguity is allowed
    {- In proof search, for every group of names
        * If exactly one succeeds, use it
        * If more than one succeeds, report an ambiguity error
        * If none succeed, move on to the next group

       This allows us to prioritise some names (e.g. to declare 'open' hints,
       which we might us to open an implementation working as a module, or to
       declare a named implementation to be used globally), and to have names
       which are only used if all else fails (e.g. as a defaulting mechanism),
       while the proof search mechanism doesn't need to know about any of the
       details.
    -}

-- Get the auto search data for a name.
export
getSearchData : {auto c : Ref Ctxt Defs} ->
                FC -> (defaults : Bool) -> Name ->
                Core SearchData
getSearchData fc defaults target
    = do defs <- get Ctxt
         Just (TCon _ _ _ dets u _ _ _) <- lookupDefExact target (gamma defs)
              | _ => undefinedName fc target
         hs <- case lookup !(toFullNames target) (typeHints defs) of
                       Just hs => filterM (\x => notHidden x (gamma defs)) hs
                       Nothing => pure []
         if defaults
            then let defns = map fst !(filterM (\x => pure $ isDefault x
                                                 && !(notHidden x (gamma defs)))
                                             (toList (autoHints defs))) in
                     pure (MkSearchData [] [(False, defns)])
            else let opens = map fst !(filterM (\x => notHidden x (gamma defs))
                                             (toList (openHints defs)))
                     autos = map fst !(filterM (\x => pure $ not (isDefault x)
                                                 && !(notHidden x (gamma defs)))
                                             (toList (autoHints defs)))
                     tyhs = map fst (filter direct hs)
                     chasers = map fst (filter (not . direct) hs) in
                     pure (MkSearchData dets (filter (isCons . snd)
                               [(False, opens),
                                (False, autos),
                                (not (uniqueAuto u), tyhs),
                                (True, chasers)]))
  where
    ||| We don't want hidden (by `%hide`) names to appear in the search.
    ||| Lookup has to be done by a full qualified name, not a resolved ID.
    notHidden : forall a. (Name, a) -> Context -> Core Bool
    notHidden (n, _) ctxt = do
      fulln <- toFullNames n
      pure $ not (isHidden fulln ctxt)

    isDefault : (Name, Bool) -> Bool
    isDefault = snd

    direct : (Name, Bool) -> Bool
    direct = snd

export
setMutWith : {auto c : Ref Ctxt Defs} ->
             FC -> Name -> List Name -> Core ()
setMutWith fc tn tns
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tn (gamma defs)
              | _ => undefinedName fc tn
         let TCon t a ps dets u _ cons det = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor [setMutWith]"))
         updateDef tn (const (Just (TCon t a ps dets u tns cons det)))

export
addMutData : {auto c : Ref Ctxt Defs} ->
             Name -> Core ()
addMutData n
    = do defs <- get Ctxt
         put Ctxt (record { mutData $= (n ::) } defs)

export
dropMutData : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
dropMutData n
    = do defs <- get Ctxt
         put Ctxt (record { mutData $= filter (/= n) } defs)

export
setDetermining : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> List Name -> Core ()
setDetermining fc tyn args
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tyn (gamma defs)
              | _ => undefinedName fc tyn
         let TCon t a ps _ u cons ms det = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor [setDetermining]"))
         apos <- getPos 0 args (type g)
         updateDef tyn (const (Just (TCon t a ps apos u cons ms det)))
  where
    -- Type isn't normalised, but the argument names refer to those given
    -- explicitly in the type, so there's no need.
    getPos : Nat -> List Name -> Term vs -> Core (List Nat)
    getPos i ns (Bind _ x (Pi _ _ _ _) sc)
        = if x `elem` ns
             then do rest <- getPos (1 + i) (filter (/=x) ns) sc
                     pure $ i :: rest
             else getPos (1 + i) ns sc
    getPos _ [] _ = pure []
    getPos _ ns ty = throw (GenericMsg fc ("Unknown determining arguments: "
                           ++ showSep ", " (map show ns)))

export
setDetags : {auto c : Ref Ctxt Defs} ->
            FC -> Name -> Maybe (List Nat) -> Core ()
setDetags fc tyn args
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tyn (gamma defs)
              | _ => undefinedName fc tyn
         let TCon t a ps det u cons ms _ = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor [setDetermining]"))
         updateDef tyn (const (Just (TCon t a ps det u cons ms args)))

export
setUniqueSearch : {auto c : Ref Ctxt Defs} ->
                  FC -> Name -> Bool -> Core ()
setUniqueSearch fc tyn u
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tyn (gamma defs)
              | _ => undefinedName fc tyn
         let TCon t a ps ds fl cons ms det = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor [setDetermining]"))
         let fl' = record { uniqueAuto = u } fl
         updateDef tyn (const (Just (TCon t a ps ds fl' cons ms det)))

export
setExternal : {auto c : Ref Ctxt Defs} ->
              FC -> Name -> Bool -> Core ()
setExternal fc tyn u
    = do defs <- get Ctxt
         Just g <- lookupCtxtExact tyn (gamma defs)
              | _ => undefinedName fc tyn
         let TCon t a ps ds fl cons ms det = definition g
              | _ => throw (GenericMsg fc (show (fullname g) ++ " is not a type constructor [setDetermining]"))
         let fl' = record { external = u } fl
         updateDef tyn (const (Just (TCon t a ps ds fl' cons ms det)))

export
addHintFor : {auto c : Ref Ctxt Defs} ->
             FC -> Name -> Name -> Bool -> Bool -> Core ()
addHintFor fc tyn_in hintn_in direct loading
    = do defs <- get Ctxt
         tyn <- toFullNames tyn_in
          -- ^ We have to index by full name because of the order we load -
          -- the name may not be resolved yet when we load the hints.
          -- Revisit if this turns out to be a bottleneck (it seems unlikely)
         hintn <- toResolvedNames hintn_in

         let hs = case lookup tyn (typeHints defs) of
                       Just hs => hs
                       Nothing => []
         if loading
            then put Ctxt
                     (record { typeHints $= insert tyn ((hintn, direct) :: hs)
                             } defs)
            else put Ctxt
                     (record { typeHints $= insert tyn ((hintn, direct) :: hs),
                               saveTypeHints $= ((tyn, hintn, direct) :: )
                             } defs)

export
addGlobalHint : {auto c : Ref Ctxt Defs} ->
                Name -> Bool -> Core ()
addGlobalHint hintn_in isdef
    = do defs <- get Ctxt
         hintn <- toResolvedNames hintn_in

         put Ctxt (record { autoHints $= insert hintn isdef,
                            saveAutoHints $= ((hintn, isdef) ::) } defs)

export
addLocalHint : {auto c : Ref Ctxt Defs} ->
               Name -> Core ()
addLocalHint hintn_in
    = do defs <- get Ctxt
         hintn <- toResolvedNames hintn_in
         put Ctxt (record { localHints $= insert hintn () } defs)

export
addOpenHint : {auto c : Ref Ctxt Defs} -> Name -> Core ()
addOpenHint hintn_in
    = do defs <- get Ctxt
         hintn <- toResolvedNames hintn_in
         put Ctxt (record { openHints $= insert hintn () } defs)

export
dropOpenHint : {auto c : Ref Ctxt Defs} -> Name -> Core ()
dropOpenHint hintn_in
    = do defs <- get Ctxt
         hintn <- toResolvedNames hintn_in
         put Ctxt (record { openHints $= delete hintn } defs)

export
setOpenHints : {auto c : Ref Ctxt Defs} -> NameMap () -> Core ()
setOpenHints hs
    = do d <- get Ctxt
         put Ctxt (record { openHints = hs } d)

export
addTransform : {auto c : Ref Ctxt Defs} ->
               FC -> Transform -> Core ()
addTransform fc t_in
    = do defs <- get Ctxt
         let Just fn_in = getFnName t_in
             | Nothing =>
                  throw (GenericMsg fc "LHS of a transformation must be a function application")
         fn <- toResolvedNames fn_in
         t <- toResolvedNames t_in
         fn_full <- toFullNames fn_in
         t_full <- toFullNames t_in
         case lookup fn (transforms defs) of
              Nothing =>
                 put Ctxt (record { transforms $= insert fn [t],
                                    saveTransforms $= ((fn_full, t_full) ::) } defs)
              Just ts =>
                 put Ctxt (record { transforms $= insert fn (t :: ts),
                                    saveTransforms $= ((fn_full, t_full) ::) } defs)

export
clearSavedHints : {auto c : Ref Ctxt Defs} -> Core ()
clearSavedHints
    = do defs <- get Ctxt
         put Ctxt (record { saveTypeHints = [],
                            saveAutoHints = [] } defs)

-- Set the default namespace for new definitions
export
setNS : {auto c : Ref Ctxt Defs} ->
        Namespace -> Core ()
setNS ns
    = do defs <- get Ctxt
         put Ctxt (record { currentNS = ns } defs)

-- Set the nested namespaces we're allowed to look inside
export
setNestedNS : {auto c : Ref Ctxt Defs} ->
              List Namespace -> Core ()
setNestedNS ns
    = do defs <- get Ctxt
         put Ctxt (record { nestedNS = ns } defs)

-- Get the default namespace for new definitions
export
getNS : {auto c : Ref Ctxt Defs} ->
        Core Namespace
getNS
    = do defs <- get Ctxt
         pure (currentNS defs)

-- Get the nested namespaces we're allowed to look inside
export
getNestedNS : {auto c : Ref Ctxt Defs} ->
              Core (List Namespace)
getNestedNS
    = do defs <- get Ctxt
         pure (nestedNS defs)

-- Add the module name, and namespace, of an imported module
-- (i.e. for "import X as Y", it's (X, Y)
-- "import public X" is, when rexported, the same as
-- "import X as [current namespace]")
export
addImported : {auto c : Ref Ctxt Defs} ->
              (ModuleIdent, Bool, Namespace) -> Core ()
addImported mod
    = do defs <- get Ctxt
         put Ctxt (record { imported $= (mod ::) } defs)

export
getImported : {auto c : Ref Ctxt Defs} ->
              Core (List (ModuleIdent, Bool, Namespace))
getImported
    = do defs <- get Ctxt
         pure (imported defs)

export
addDirective : {auto c : Ref Ctxt Defs} ->
               String -> String -> Core ()
addDirective c str
    = do defs <- get Ctxt
         case getCG (options defs) c of
              Nothing => -- warn, rather than fail, because the CG may exist
                         -- but be unknown to this particular instance
                         coreLift $ putStrLn $ "Unknown code generator " ++ c
              Just cg => put Ctxt (record { cgdirectives $= ((cg, str) ::) } defs)

export
getDirectives : {auto c : Ref Ctxt Defs} ->
                CG -> Core (List String)
getDirectives cg
    = do defs <- get Ctxt
         pure $ defs.options.session.directives ++
                 mapMaybe getDir (cgdirectives defs)
  where
    getDir : (CG, String) -> Maybe String
    getDir (x', str) = if cg == x' then Just str else Nothing

export
getNextTypeTag : {auto c : Ref Ctxt Defs} ->
                 Core Int
getNextTypeTag
    = do defs <- get Ctxt
         put Ctxt (record { nextTag $= (+1) } defs)
         pure (nextTag defs)

-- Add a new nested namespace to the current namespace for new definitions
-- e.g. extendNS ["Data"] when namespace is "Prelude.List" leads to
-- current namespace of "Prelude.List.Data"
-- Inner namespaces go first, for ease of name lookup
export
extendNS : {auto c : Ref Ctxt Defs} ->
           Namespace -> Core ()
extendNS ns
    = do defs <- get Ctxt
         put Ctxt (record { currentNS $= (<.> ns) } defs)

export
withExtendedNS : {auto c : Ref Ctxt Defs} ->
                 Namespace -> Core a -> Core a
withExtendedNS ns act
    = do defs <- get Ctxt
         let cns = currentNS defs
         put Ctxt (record { currentNS = cns <.> ns } defs)
         ma <- catch (Right <$> act) (pure . Left)
         defs <- get Ctxt
         put Ctxt (record { currentNS = cns } defs)
         case ma of
           Left err => throw err
           Right a  => pure a

-- Get the name as it would be defined in the current namespace
-- i.e. if it doesn't have an explicit namespace already, add it,
-- otherwise leave it alone
export
inCurrentNS : {auto c : Ref Ctxt Defs} ->
              Name -> Core Name
inCurrentNS (UN n)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) (UN n))
inCurrentNS n@(CaseBlock _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n@(WithBlock _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n@(Nested _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n@(MN _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n@(DN _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n@(RF _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n = pure n

export
setVisible : {auto c : Ref Ctxt Defs} ->
             Namespace -> Core ()
setVisible nspace
    = do defs <- get Ctxt
         put Ctxt (record { gamma->visibleNS $= (nspace ::) } defs)

export
getVisible : {auto c : Ref Ctxt Defs} ->
             Core (List Namespace)
getVisible
    = do defs <- get Ctxt
         pure (visibleNS (gamma defs))

-- set whether all names should be viewed as public. Be careful with this,
-- it's not intended for when checking user code! It's meant for allowing
-- easy checking of partially evaluated definitions.
export
setAllPublic : {auto c : Ref Ctxt Defs} ->
               (pub : Bool) -> Core ()
setAllPublic pub
    = do defs <- get Ctxt
         put Ctxt (record { gamma->allPublic = pub } defs)

export
isAllPublic : {auto c : Ref Ctxt Defs} ->
              Core Bool
isAllPublic
    = do defs <- get Ctxt
         pure (allPublic (gamma defs))

-- Return True if the given namespace is visible in the context (meaning
-- the namespace itself, and any namespace it's nested inside)
export
isVisible : {auto c : Ref Ctxt Defs} ->
            Namespace -> Core Bool
isVisible nspace
    = do defs <- get Ctxt
         pure (any visible (allParents (currentNS defs) ++
                            nestedNS defs ++
                            visibleNS (gamma defs)))

  where
    -- Visible if any visible namespace is a parent of the namespace we're
    -- asking about
    visible : Namespace -> Bool
    visible visns = isParentOf visns nspace

-- Get the next entry id in the context (this is for recording where to go
-- back to when backtracking in the elaborator)
export
getNextEntry : {auto c : Ref Ctxt Defs} ->
               Core Int
getNextEntry
    = do defs <- get Ctxt
         pure (nextEntry (gamma defs))

export
setNextEntry : {auto c : Ref Ctxt Defs} ->
               Int -> Core ()
setNextEntry i
    = do defs <- get Ctxt
         put Ctxt (record { gamma->nextEntry = i } defs)

-- Set the 'first entry' index (i.e. the first entry in the current file)
-- to the place we currently are in the context
export
resetFirstEntry : {auto c : Ref Ctxt Defs} ->
                  Core ()
resetFirstEntry
    = do defs <- get Ctxt
         put Ctxt (record { gamma->firstEntry = nextEntry (gamma defs) } defs)

export
getFullName : {auto c : Ref Ctxt Defs} ->
              Name -> Core Name
getFullName (Resolved i)
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
              | Nothing => pure (Resolved i)
         pure (fullname gdef)
getFullName n = pure n

-- Getting and setting various options

export
getPPrint : {auto c : Ref Ctxt Defs} ->
            Core PPrinter
getPPrint
    = do defs <- get Ctxt
         pure (printing (options defs))

export
setPPrint : {auto c : Ref Ctxt Defs} ->
            PPrinter -> Core ()
setPPrint ppopts
    = do defs <- get Ctxt
         put Ctxt (record { options->printing = ppopts } defs)

export
setCG : {auto c : Ref Ctxt Defs} ->
        CG -> Core ()
setCG cg
    = do defs <- get Ctxt
         put Ctxt (record { options->session->codegen = cg } defs)

export
getDirs : {auto c : Ref Ctxt Defs} -> Core Dirs
getDirs
    = do defs <- get Ctxt
         pure (dirs (options defs))

export
addExtraDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
addExtraDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->extra_dirs $= (++ [dir]) } defs)

export
addPackageDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
addPackageDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->package_dirs $= (++ [dir]) } defs)

export
addDataDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
addDataDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->data_dirs $= (++ [dir]) } defs)

export
addLibDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
addLibDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->lib_dirs $= (++ [dir]) } defs)

export
setBuildDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
setBuildDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->build_dir = dir } defs)

export
setDependsDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
setDependsDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->depends_dir = dir } defs)

export
setOutputDir : {auto c : Ref Ctxt Defs} -> Maybe String -> Core ()
setOutputDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->output_dir = dir } defs)

export
setSourceDir : {auto c : Ref Ctxt Defs} -> Maybe String -> Core ()
setSourceDir mdir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->source_dir = mdir } defs)

export
setWorkingDir : {auto c : Ref Ctxt Defs} -> String -> Core ()
setWorkingDir dir
    = do defs <- get Ctxt
         coreLift_ $ changeDir dir
         Just cdir <- coreLift $ currentDir
              | Nothing => throw (InternalError "Can't get current directory")
         put Ctxt (record { options->dirs->working_dir = cdir } defs)

export
getWorkingDir : Core String
getWorkingDir
    = do Just d <- coreLift $ currentDir
              | Nothing => throw (InternalError "Can't get current directory")
         pure d

export
withCtxt : {auto c : Ref Ctxt Defs} -> Core a -> Core a
withCtxt = wrapRef Ctxt resetCtxt
  where
    resetCtxt : Defs -> Core ()
    resetCtxt defs = do let dir = defs.options.dirs.working_dir
                        coreLift_ $ changeDir dir

export
setPrefix : {auto c : Ref Ctxt Defs} -> String -> Core ()
setPrefix dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->prefix_dir = dir } defs)

export
setExtension : {auto c : Ref Ctxt Defs} -> LangExt -> Core ()
setExtension e
    = do defs <- get Ctxt
         put Ctxt (record { options $= setExtension e } defs)

export
isExtension : LangExt -> Defs -> Bool
isExtension e defs = isExtension e (options defs)

export
checkUnambig : {auto c : Ref Ctxt Defs} ->
               FC -> Name -> Core Name
checkUnambig fc n
    = do defs <- get Ctxt
         case !(lookupDefName n (gamma defs)) of
              [] => undefinedName fc n
              [(fulln, i, _)] => pure (Resolved i)
              ns => throw (AmbiguousName fc (map fst ns))

export
lazyActive : {auto c : Ref Ctxt Defs} ->
             Bool -> Core ()
lazyActive a
    = do defs <- get Ctxt
         put Ctxt (record { options->elabDirectives->lazyActive = a } defs)

export
setUnboundImplicits : {auto c : Ref Ctxt Defs} ->
                Bool -> Core ()
setUnboundImplicits a
    = do defs <- get Ctxt
         put Ctxt (record { options->elabDirectives->unboundImplicits = a } defs)

export
setPrefixRecordProjections : {auto c : Ref Ctxt Defs} -> Bool -> Core ()
setPrefixRecordProjections b = do
  defs <- get Ctxt
  put Ctxt (record { options->elabDirectives->prefixRecordProjections = b } defs)

export
setDefaultTotalityOption : {auto c : Ref Ctxt Defs} ->
                           TotalReq -> Core ()
setDefaultTotalityOption tot
    = do defs <- get Ctxt
         put Ctxt (record { options->elabDirectives->totality = tot } defs)

export
setAmbigLimit : {auto c : Ref Ctxt Defs} ->
                Nat -> Core ()
setAmbigLimit max
    = do defs <- get Ctxt
         put Ctxt (record { options->elabDirectives->ambigLimit = max } defs)

export
setAutoImplicitLimit : {auto c : Ref Ctxt Defs} ->
                       Nat -> Core ()
setAutoImplicitLimit max
    = do defs <- get Ctxt
         put Ctxt (record { options->elabDirectives->autoImplicitLimit = max } defs)

export
setNFThreshold : {auto c : Ref Ctxt Defs} ->
                 Nat -> Core ()
setNFThreshold max
    = do defs <- get Ctxt
         put Ctxt (record { options->elabDirectives->nfThreshold = max } defs)

export
setSearchTimeout : {auto c : Ref Ctxt Defs} ->
                   Integer -> Core ()
setSearchTimeout t
    = do defs <- get Ctxt
         put Ctxt (record { options->session->searchTimeout = t } defs)

export
isLazyActive : {auto c : Ref Ctxt Defs} ->
               Core Bool
isLazyActive
    = do defs <- get Ctxt
         pure (lazyActive (elabDirectives (options defs)))

export
isUnboundImplicits : {auto c : Ref Ctxt Defs} ->
                  Core Bool
isUnboundImplicits
    = do defs <- get Ctxt
         pure (unboundImplicits (elabDirectives (options defs)))

export
isPrefixRecordProjections : {auto c : Ref Ctxt Defs} -> Core Bool
isPrefixRecordProjections =
  prefixRecordProjections . elabDirectives . options <$> get Ctxt

export
getDefaultTotalityOption : {auto c : Ref Ctxt Defs} ->
                           Core TotalReq
getDefaultTotalityOption
    = do defs <- get Ctxt
         pure (totality (elabDirectives (options defs)))

export
getAmbigLimit : {auto c : Ref Ctxt Defs} ->
                Core Nat
getAmbigLimit
    = do defs <- get Ctxt
         pure (ambigLimit (elabDirectives (options defs)))

export
getAutoImplicitLimit : {auto c : Ref Ctxt Defs} ->
                       Core Nat
getAutoImplicitLimit
    = do defs <- get Ctxt
         pure (autoImplicitLimit (elabDirectives (options defs)))

export
setPair : {auto c : Ref Ctxt Defs} ->
          FC -> (pairType : Name) -> (fstn : Name) -> (sndn : Name) ->
          Core ()
setPair fc ty f s
    = do defs <- get Ctxt
         ty' <- checkUnambig fc ty
         f' <- checkUnambig fc f
         s' <- checkUnambig fc s
         put Ctxt (record { options $= setPair ty' f' s' } defs)

export
setRewrite : {auto c : Ref Ctxt Defs} ->
             FC -> (eq : Name) -> (rwlemma : Name) -> Core ()
setRewrite fc eq rw
    = do defs <- get Ctxt
         rw' <- checkUnambig fc rw
         eq' <- checkUnambig fc eq
         put Ctxt (record { options $= setRewrite eq' rw' } defs)

-- Don't check for ambiguity here; they're all meant to be overloadable
export
setFromInteger : {auto c : Ref Ctxt Defs} ->
                 Name -> Core ()
setFromInteger n
    = do defs <- get Ctxt
         put Ctxt (record { options $= setFromInteger n } defs)

export
setFromString : {auto c : Ref Ctxt Defs} ->
                Name -> Core ()
setFromString n
    = do defs <- get Ctxt
         put Ctxt (record { options $= setFromString n } defs)

export
setFromChar : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
setFromChar n
    = do defs <- get Ctxt
         put Ctxt (record { options $= setFromChar n } defs)

export
setFromDouble : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
setFromDouble n
    = do defs <- get Ctxt
         put Ctxt (record { options $= setFromDouble n } defs)

export
addNameDirective : {auto c : Ref Ctxt Defs} ->
                   FC -> Name -> List String -> Core ()
addNameDirective fc n ns
    = do defs <- get Ctxt
         n' <- checkUnambig fc n
         put Ctxt (record { namedirectives $= insert n' ns  } defs)

-- Checking special names from Options

export
isPairType : {auto c : Ref Ctxt Defs} ->
             Name -> Core Bool
isPairType n
    = do defs <- get Ctxt
         case pairnames (options defs) of
              Nothing => pure False
              Just l => pure $ !(getFullName n) == !(getFullName (pairType l))

export
fstName : {auto c : Ref Ctxt Defs} ->
          Core (Maybe Name)
fstName
    = do defs <- get Ctxt
         pure $ maybe Nothing (Just . fstName) (pairnames (options defs))

export
sndName : {auto c : Ref Ctxt Defs} ->
          Core (Maybe Name)
sndName
    = do defs <- get Ctxt
         pure $ maybe Nothing (Just . sndName) (pairnames (options defs))

export
getRewrite :{auto c : Ref Ctxt Defs} ->
            Core (Maybe Name)
getRewrite
    = do defs <- get Ctxt
         pure $ maybe Nothing (Just . rewriteName) (rewritenames (options defs))

export
isEqualTy : {auto c : Ref Ctxt Defs} ->
            Name -> Core Bool
isEqualTy n
    = do defs <- get Ctxt
         case rewritenames (options defs) of
              Nothing => pure False
              Just r => pure $ !(getFullName n) == !(getFullName (equalType r))

export
fromIntegerName : {auto c : Ref Ctxt Defs} ->
                  Core (Maybe Name)
fromIntegerName
    = do defs <- get Ctxt
         pure $ fromIntegerName (primnames (options defs))

export
fromStringName : {auto c : Ref Ctxt Defs} ->
                 Core (Maybe Name)
fromStringName
    = do defs <- get Ctxt
         pure $ fromStringName (primnames (options defs))

export
fromCharName : {auto c : Ref Ctxt Defs} ->
               Core (Maybe Name)
fromCharName
    = do defs <- get Ctxt
         pure $ fromCharName (primnames (options defs))

export
fromDoubleName : {auto c : Ref Ctxt Defs} ->
               Core (Maybe Name)
fromDoubleName
    = do defs <- get Ctxt
         pure $ fromDoubleName (primnames (options defs))

export
getPrimNames : {auto c : Ref Ctxt Defs} -> Core PrimNames
getPrimNames = [| MkPrimNs fromIntegerName fromStringName fromCharName fromDoubleName |]

export
getPrimitiveNames : {auto c : Ref Ctxt Defs} -> Core (List Name)
getPrimitiveNames = primNamesToList <$> getPrimNames

export
addLogLevel : {auto c : Ref Ctxt Defs} ->
              Maybe LogLevel -> Core ()
addLogLevel lvl
    = do defs <- get Ctxt
         case lvl of
           Nothing => put Ctxt (record { options->session->logEnabled = True,
                                         options->session->logLevel = defaultLogLevel } defs)
           Just l  => put Ctxt (record { options->session->logEnabled = True,
                                         options->session->logLevel $= insertLogLevel l } defs)

export
withLogLevel : {auto c : Ref Ctxt Defs} ->
               LogLevel -> Core a -> Core a
withLogLevel l comp = do
  defs <- get Ctxt
  let logs = logLevel (session (options defs))
  put Ctxt (record { options->session->logLevel = insertLogLevel l logs } defs)
  r <- comp
  defs <- get Ctxt
  put Ctxt (record { options->session->logLevel = logs } defs)
  pure r

export
setLogTimings : {auto c : Ref Ctxt Defs} ->
                Bool -> Core ()
setLogTimings b
    = do defs <- get Ctxt
         put Ctxt (record { options->session->logTimings = b } defs)

export
setDebugElabCheck : {auto c : Ref Ctxt Defs} ->
                    Bool -> Core ()
setDebugElabCheck b
    = do defs <- get Ctxt
         put Ctxt (record { options->session->debugElabCheck = b } defs)

export
getSession : {auto c : Ref Ctxt Defs} ->
             Core Session
getSession
    = do defs <- get Ctxt
         pure (session (options defs))

export
setSession : {auto c : Ref Ctxt Defs} ->
             Session -> Core ()
setSession sopts
    = do defs <- get Ctxt
         put Ctxt (record { options->session = sopts } defs)

export
recordWarning : {auto c : Ref Ctxt Defs} -> Warning -> Core ()
recordWarning w
    = do defs <- get Ctxt
         session <- getSession
         put Ctxt $ record { warnings $= (w ::) } defs

export
getTime : Core Integer
getTime
    = do clock <- coreLift (clockTime Process)
         pure (seconds clock * nano + nanoseconds clock)
  where
    nano : Integer
    nano = 1000000000

-- A simple timeout mechanism. We can start a timer, clear it, or check
-- whether too much time has passed and throw an exception if so

||| Initialise the timer, setting the time in milliseconds after which a
||| timeout should be thrown.
||| Note: It's important to clear the timer when the operation that might
||| timeout is complete, otherwise something else might throw a timeout
||| error!
export
startTimer : {auto c : Ref Ctxt Defs} ->
             Integer -> String -> Core ()
startTimer tmax action
    = do t <- getTime
         defs <- get Ctxt
         put Ctxt $ record { timer = Just (t + tmax * 1000000, action) } defs

||| Clear the timer
export
clearTimer : {auto c : Ref Ctxt Defs} -> Core ()
clearTimer
    = do defs <- get Ctxt
         put Ctxt $ record { timer = Nothing } defs

||| If the timer was started more than t milliseconds ago, throw an exception
export
checkTimer : {auto c : Ref Ctxt Defs} ->
             Core ()
checkTimer
    = do defs <- get Ctxt
         let Just (max, action) = timer defs
                | Nothing => pure ()
         t <- getTime
         if (t > max)
            then throw (Timeout action)
            else pure ()

-- Update the list of imported incremental compile data, if we're in
-- incremental mode for the current CG
export
addImportedInc : {auto c : Ref Ctxt Defs} ->
                 ModuleIdent -> List (CG, String, List String) -> Core ()
addImportedInc modNS inc
    = do s <- getSession
         let cg = s.codegen
         defs <- get Ctxt
         when (cg `elem` s.incrementalCGs) $
           case lookup cg inc of
                Nothing =>
                  -- No incremental compile data for current CG, so we can't
                  -- compile incrementally
                  do recordWarning (GenericWarn ("No incremental compile data for " ++ show modNS))
                     defs <- get Ctxt
                     put Ctxt (record { allIncData $= drop cg } defs)
                Just (mods, extra) =>
                     put Ctxt (record { allIncData $= addMod cg (mods, extra) }
                                      defs)
  where
    addMod : CG -> (String, List String) ->
             List (CG, (List String, List String)) ->
             List (CG, (List String, List String))
    addMod cg (mod, all) [] = [(cg, ([mod], all))]
    addMod cg (mod, all) ((cg', (mods, libs)) :: xs)
        = if cg == cg'
             then ((cg, (mod :: mods, libs ++ all)) :: xs)
             else ((cg', (mods, libs)) :: addMod cg (mod, all) xs)

    drop : CG -> List (CG, a) -> List (CG, a)
    drop cg [] = []
    drop cg ((x, v) :: xs)
        = if cg == x
             then xs
             else ((x, v) :: drop cg xs)

export
setIncData : {auto c : Ref Ctxt Defs} ->
             CG -> (String, List String) -> Core ()
setIncData cg res
    = do defs <- get Ctxt
         put Ctxt (record { incData $= ((cg, res) :: )} defs)
