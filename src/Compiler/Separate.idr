module Compiler.Separate

import public Core.FC
import public Core.Name
import public Core.Name.Namespace
import public Core.CompileExpr
import public Compiler.VMCode
import public Libraries.Data.Graph
import public Libraries.Data.SortedMap
import public Libraries.Data.SortedSet
import public Libraries.Data.StringMap

import Core.Hash
import Core.TT
import Data.List
import Data.List1
import Data.Vect
import Data.Maybe

%default covering

-- Compilation unit IDs are intended to be opaque,
-- just to be able to express dependencies via keys in a map and such.
export
record CompilationUnitId where
  constructor CUID
  int : Int

export
Eq CompilationUnitId where
  CUID x == CUID y = x == y

export
Ord CompilationUnitId where
  compare (CUID x) (CUID y) = compare x y

export
Hashable CompilationUnitId where
  hashWithSalt h (CUID int) = hashWithSalt h int

||| A compilation unit is a set of namespaces.
|||
||| The record is parameterised by the type of the definition,
||| which makes it reusable for various IRs provided by getCompileData.
public export
record CompilationUnit def where
  constructor MkCompilationUnit

  ||| Unique identifier of a compilation unit within a CompilationUnitInfo record.
  id : CompilationUnitId

  ||| Namespaces contained within the compilation unit.
  namespaces : List1 Namespace

  ||| Other units that this unit depends on.
  dependencies : SortedSet CompilationUnitId

  ||| The definitions belonging into this compilation unit.
  definitions : List (Name, def)

export
Hashable def => Hashable (CompilationUnit def) where
  hashWithSalt h cu =
    h `hashWithSalt` SortedSet.toList cu.dependencies
      `hashWithSalt` cu.definitions

private
getNS : Name -> Namespace
getNS (NS ns _) = ns
getNS _ = emptyNS

||| Group definitions by namespace.
private
splitByNS : List (Name, def) -> List (Namespace, List (Name, def))
splitByNS = SortedMap.toList . foldl addOne SortedMap.empty
  where
    addOne
      : SortedMap Namespace (List (Name, def))
      -> (Name, def)
      -> SortedMap Namespace (List (Name, def))
    addOne nss ndef@(n, _) =
      SortedMap.mergeWith
        (++)
        (SortedMap.singleton (getNS n) [ndef])
        nss

public export
interface HasNamespaces a where
  ||| Return the set of namespaces mentioned within
  nsRefs : a -> SortedSet Namespace

-- For now, we have instances only for NamedDef and VMDef.
-- For other IR representations, we'll have to add more instances.
-- This is not hard, just a bit of tedious mechanical work.
mutual
  export
  HasNamespaces NamedCExp where
    nsRefs (NmLocal fc n) = SortedSet.empty
    nsRefs (NmRef fc n) = SortedSet.singleton $ getNS n
    nsRefs (NmLam fc n rhs) = nsRefs rhs
    nsRefs (NmLet fc n val rhs) = nsRefs val <+> nsRefs rhs
    nsRefs (NmApp fc f args) = nsRefs f <+> concatMap nsRefs args
    nsRefs (NmCon fc cn ci tag args) = concatMap nsRefs args
    nsRefs (NmForce fc reason rhs) = nsRefs rhs
    nsRefs (NmDelay fc reason rhs) = nsRefs rhs
    nsRefs (NmErased fc) = SortedSet.empty
    nsRefs (NmPrimVal ft x) = SortedSet.empty
    nsRefs (NmOp fc op args) = concatMap nsRefs args
    nsRefs (NmExtPrim fc n args) = concatMap nsRefs args
    nsRefs (NmConCase fc scrut alts mbDflt) =
      nsRefs scrut <+> concatMap nsRefs alts <+> concatMap nsRefs mbDflt
    nsRefs (NmConstCase fc scrut alts mbDflt) =
      nsRefs scrut <+> concatMap nsRefs alts <+> concatMap nsRefs mbDflt
    nsRefs (NmCrash fc msg) = SortedSet.empty

  export
  HasNamespaces NamedConAlt where
    nsRefs (MkNConAlt n ci tag args rhs) = nsRefs rhs

  export
  HasNamespaces NamedConstAlt where
    nsRefs (MkNConstAlt c rhs) = nsRefs rhs

  export
  HasNamespaces NamedDef where
    nsRefs (MkNmFun argNs rhs) = nsRefs rhs
    nsRefs (MkNmCon tag arity nt) = SortedSet.empty
    nsRefs (MkNmForeign ccs fargs rty) = SortedSet.empty
    nsRefs (MkNmError rhs) = nsRefs rhs

export
HasNamespaces VMInst where
  nsRefs (DECLARE x) = empty
  nsRefs START = empty
  nsRefs (ASSIGN x y) = empty
  nsRefs (MKCON x tag args) = empty
  nsRefs (MKCLOSURE x n missing args) = singleton $ getNS n
  nsRefs (MKCONSTANT x y) = empty
  nsRefs (APPLY x f a) = empty
  nsRefs (CALL x tailpos n args) = singleton $ getNS n
  nsRefs (OP x y xs) = empty
  nsRefs (EXTPRIM x n xs) = singleton $ getNS n
  nsRefs (CASE x alts def) =
    maybe empty (concatMap nsRefs) def <+>
    concatMap ((concatMap nsRefs) . snd) alts
  nsRefs (CONSTCASE x alts def) =
    maybe empty (concatMap nsRefs) def <+>
    concatMap ((concatMap nsRefs) . snd) alts
  nsRefs (PROJECT x value pos) = empty
  nsRefs (NULL x) = empty
  nsRefs (ERROR x) = empty

export
HasNamespaces VMDef where
  nsRefs (MkVMFun args is) = concatMap nsRefs is
  nsRefs (MkVMForeign _ _ _) = empty
  nsRefs (MkVMError is) = concatMap nsRefs is


-- a slight hack for convenient use with CompileData.namedDefs
export
HasNamespaces a => HasNamespaces (FC, a) where
  nsRefs (_, x) = nsRefs x

-- another slight hack for convenient use with CompileData.namedDefs
export
Hashable def => Hashable (FC, def) where
  -- ignore FC in hash, like everywhere else
  hashWithSalt h (fc, x) = hashWithSalt h x

||| Output of the codegen separation algorithm.
||| Should contain everything you need in a separately compiling codegen.
public export
record CompilationUnitInfo def where
  constructor MkCompilationUnitInfo

  ||| Compilation units computed from the given definitions,
  ||| ordered topologically, starting from units depending on no other unit.
  compilationUnits : List (CompilationUnit def)

  ||| Mapping from ID to CompilationUnit.
  byId : SortedMap CompilationUnitId (CompilationUnit def)

  ||| Maps each namespace to the compilation unit that contains it.
  namespaceMap : SortedMap Namespace CompilationUnitId

||| Group the given definitions into compilation units for separate code generation.
export
getCompilationUnits : HasNamespaces def => List (Name, def) -> CompilationUnitInfo def
getCompilationUnits {def} defs =
  let
    -- Definitions grouped by namespace.
    defsByNS : SortedMap Namespace (List (Name, def))
      = SortedMap.fromList $ splitByNS defs

    -- Mapping from a namespace to all namespaces mentioned within.
    -- Represents graph edges pointing in that direction.
    nsDeps : SortedMap Namespace (SortedSet Namespace)
      = foldl (SortedMap.mergeWith SortedSet.union) SortedMap.empty
          [ SortedMap.singleton (getNS n) (SortedSet.delete (getNS n) (nsRefs d))
          | (n, d) <- defs
          ]

    -- Strongly connected components of the NS dep graph,
    -- ordered by output degree ascending.
    --
    -- Each SCC will become a compilation unit.
    components : List (List1 Namespace)
      = List.reverse $ tarjan nsDeps  -- tarjan generates reverse toposort

    -- Maps a namespace to the compilation unit that contains it.
    nsMap : SortedMap Namespace CompilationUnitId
      = SortedMap.fromList [(ns, cuid) | (cuid, nss) <- withCUID components, ns <- List1.forget nss]

    -- List of all compilation units, ordered by number of dependencies, ascending.
    units : List (CompilationUnit def)
      = [mkUnit nsDeps nsMap defsByNS cuid nss | (cuid, nss) <- withCUID components]

  in MkCompilationUnitInfo
      { compilationUnits = units
      , byId = SortedMap.fromList [(unit.id, unit) | unit <- units]
      , namespaceMap = nsMap
      }

  where
    withCUID : List a -> List (CompilationUnitId, a)
    withCUID xs = [(CUID $ cast i, x) | (i, x) <- zip [0..length xs] xs]

    ||| Wrap all information in a compilation unit record.
    mkUnit :
      SortedMap Namespace (SortedSet Namespace)
      -> SortedMap Namespace CompilationUnitId
      -> SortedMap Namespace (List (Name, def))
      -> CompilationUnitId -> List1 Namespace -> CompilationUnit def
    mkUnit nsDeps nsMap defsByNS cuid nss =
      MkCompilationUnit
      { id = cuid
      , namespaces = nss
      , dependencies = SortedSet.delete cuid dependencies
      , definitions = definitions
      }
     where
      dependencies : SortedSet CompilationUnitId
      dependencies = SortedSet.fromList $ do
        ns <- List1.forget nss  -- NS contained within
        depsNS <- SortedSet.toList $  -- NS we depend on
          fromMaybe SortedSet.empty $
            SortedMap.lookup ns nsDeps

        case SortedMap.lookup depsNS nsMap of
          Nothing => []
          Just depCUID => [depCUID]

      definitions : List (Name, def)
      definitions = concat [fromMaybe [] $ SortedMap.lookup ns defsByNS | ns <- nss]
