-- Representation of expressions ready for compiling
-- Type erased, explicit case trees
module Core.CompileExpr

import Core.FC
import Core.Name
import Core.TT

import Data.List
import Libraries.Data.NameMap
import Data.Vect

%default covering

-- Backends might be able to treat some 'shapes' of data type specially,
-- e.g. enumerations or lists.
-- They can use or ignore this information as they see fit.
public export
data ConInfo = DATACON -- normal data constructor
             | TYCON -- normal type constructor
             | NIL -- nil of a list or option shaped thing
             | CONS -- cons of a list shaped thing
             | ENUM -- part of an enumeration
             | NOTHING -- nothing of an option shaped thing
             | JUST -- just of an option shaped thing
             | RECORD -- record constructor (no tag)

export
Show ConInfo where
  show DATACON = "[datacon]"
  show TYCON   = "[tycon]"
  show NIL     = "[nil]"
  show CONS    = "[cons]"
  show ENUM    = "[enum]"
  show NOTHING = "[nothing]"
  show JUST    = "[just]"
  show RECORD  = "[record]"

export
Eq ConInfo where
  DATACON == DATACON = True
  TYCON == TYCON = True
  NIL == NIL = True
  CONS == CONS = True
  ENUM == ENUM = True
  NOTHING == NOTHING = True
  JUST == JUST = True
  RECORD == RECORD = True
  _ == _ = False

mutual
  ||| CExp - an expression ready for compiling.
  public export
  data CExp : List Name -> Type where
       CLocal : {idx : Nat} -> FC -> (0 p : IsVar x idx vars) -> CExp vars
       CRef : FC -> Name -> CExp vars
       -- Lambda expression
       CLam : FC -> (x : Name) -> CExp (x :: vars) -> CExp vars
       -- Let bindings
       CLet : FC -> (x : Name) -> (inlineOK : Bool) -> -- Don't inline if set
              CExp vars -> CExp (x :: vars) -> CExp vars
       -- Application of a defined function. The length of the argument list is
       -- exactly the same length as expected by its definition (so saturate with
       -- lambdas if necessary, or overapply with additional CApps)
       CApp : FC -> CExp vars -> List (CExp vars) -> CExp vars
       -- A saturated constructor application
       -- 'ConInfo' gives additional information about the constructor that
       -- a back end might be able to use. It is ignorable.
       CCon : FC -> Name -> ConInfo -> (tag : Int) ->
              List (CExp vars) -> CExp vars
       -- Internally defined primitive operations
       COp : {arity : _} ->
             FC -> PrimFn arity -> Vect arity (CExp vars) -> CExp vars
       -- Externally defined primitive operations
       CExtPrim : FC -> (p : Name) -> List (CExp vars) -> CExp vars
       -- A forced (evaluated) value
       CForce : FC -> LazyReason -> CExp vars -> CExp vars
       -- A delayed value
       CDelay : FC -> LazyReason -> CExp vars -> CExp vars
       -- A case match statement
       CConCase : FC -> (sc : CExp vars) -> List (CConAlt vars) -> Maybe (CExp vars) -> CExp vars
       CConstCase : FC -> (sc : CExp vars) -> List (CConstAlt vars) -> Maybe (CExp vars) -> CExp vars
       -- A primitive value
       CPrimVal : FC -> Constant -> CExp vars
       -- An erased value
       CErased : FC -> CExp vars
       -- Some sort of crash?
       CCrash : FC -> String -> CExp vars

  public export
  data CConAlt : List Name -> Type where
       -- If no tag, then match by constructor name. Back ends might want to
       -- convert names to a unique integer for performance.
       MkConAlt : Name -> ConInfo -> (tag : Int) -> (args : List Name) ->
                  CExp (args ++ vars) -> CConAlt vars

  public export
  data CConstAlt : List Name -> Type where
       MkConstAlt : Constant -> CExp vars -> CConstAlt vars

mutual
  ||| NamedCExp - as above, but without the name index, so with explicit
  ||| names, which are faster (but less safe) to manipulate in the inliner.
  ||| You can, howeveer, assume that name bindings are unique - translation
  ||| to this form (and the liner) ensure that, even if the type doesn't
  ||| guarantee it!
  public export
  data NamedCExp : Type where
       NmLocal : FC -> Name -> NamedCExp
       NmRef : FC -> Name -> NamedCExp
       -- Lambda expression
       NmLam : FC -> (x : Name) -> NamedCExp -> NamedCExp
       -- Let bindings
       NmLet : FC -> (x : Name) -> NamedCExp -> NamedCExp -> NamedCExp
       -- Application of a defined function. The length of the argument list is
       -- exactly the same length as expected by its definition (so saturate with
       -- lambdas if necessary, or overapply with additional CApps)
       NmApp : FC -> NamedCExp -> List NamedCExp -> NamedCExp
       -- A saturated constructor application
       -- 'ConInfo' gives additional information about the constructor that
       -- a back end might be able to use. It is ignoreable.
       NmCon : FC -> Name -> ConInfo -> (tag : Int) ->
               List NamedCExp -> NamedCExp
       -- Internally defined primitive operations
       NmOp : {arity : _ } -> FC -> PrimFn arity -> Vect arity NamedCExp -> NamedCExp
       -- Externally defined primitive operations
       NmExtPrim : FC -> (p : Name) -> List NamedCExp -> NamedCExp
       -- A forced (evaluated) value
       NmForce : FC -> LazyReason -> NamedCExp -> NamedCExp
       -- A delayed value
       NmDelay : FC -> LazyReason -> NamedCExp -> NamedCExp
       -- A case match statement
       NmConCase : FC -> (sc : NamedCExp) -> List NamedConAlt -> Maybe NamedCExp -> NamedCExp
       NmConstCase : FC -> (sc : NamedCExp) -> List NamedConstAlt -> Maybe NamedCExp -> NamedCExp
       -- A primitive value
       NmPrimVal : FC -> Constant -> NamedCExp
       -- An erased value
       NmErased : FC -> NamedCExp
       -- Some sort of crash?
       NmCrash : FC -> String -> NamedCExp

  public export
  data NamedConAlt : Type where
       MkNConAlt : Name -> ConInfo -> (tag : Int) -> (args : List Name) ->
                   NamedCExp -> NamedConAlt

  public export
  data NamedConstAlt : Type where
       MkNConstAlt : Constant -> NamedCExp -> NamedConstAlt

-- Argument type descriptors for foreign function calls
public export
data CFType : Type where
     CFUnit : CFType
     CFInt : CFType
     CFInt8 : CFType
     CFInt16 : CFType
     CFInt32 : CFType
     CFInt64 : CFType
     CFUnsigned8 : CFType
     CFUnsigned16 : CFType
     CFUnsigned32 : CFType
     CFUnsigned64 : CFType
     CFString : CFType
     CFDouble : CFType
     CFChar : CFType
     CFPtr : CFType
     CFGCPtr : CFType
     CFBuffer : CFType
     CFWorld : CFType
     CFFun : CFType -> CFType -> CFType
     CFIORes : CFType -> CFType
     CFStruct : String -> List (String, CFType) -> CFType
     CFUser : Name -> List CFType -> CFType

public export
data CDef : Type where
     -- Normal function definition
     MkFun : (args : List Name) -> CExp args -> CDef
     -- Constructor
     MkCon : (tag : Int) -> (arity : Nat) -> (nt : Maybe Nat) -> CDef
     -- Foreign definition
     MkForeign : (ccs : List String) ->
                 (fargs : List CFType) ->
                 CFType ->
                 CDef
     -- A function which will fail at runtime (usually due to being a hole) so needs
     -- to run, discarding arguments, no matter how many arguments are passed
     MkError : CExp [] -> CDef

public export
data NamedDef : Type where
     -- Normal function definition
     MkNmFun : (args : List Name) -> NamedCExp -> NamedDef
     -- Constructor
     MkNmCon : (tag : Int) -> (arity : Nat) -> (nt : Maybe Nat) -> NamedDef
     -- Foreign definition
     MkNmForeign : (ccs : List String) ->
                   (fargs : List CFType) ->
                   CFType ->
                   NamedDef
     -- A function which will fail at runtime (usually due to being a hole) so needs
     -- to run, discarding arguments, no matter how many arguments are passed
     MkNmError : NamedCExp -> NamedDef

mutual
  export
  Show NamedCExp where
    show (NmLocal _ x) = "!" ++ show x
    show (NmRef _ x) = show x
    show (NmLam _ x y) = "(%lam " ++ show x ++ " " ++ show y ++ ")"
    show (NmLet _ x y z) = "(%let " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (NmApp _ x xs)
        = assert_total $ "(" ++ show x ++ " " ++ show xs ++ ")"
    show (NmCon _ x ci tag xs)
        = assert_total $ "(%con " ++ showFlag ci ++ show x ++ " " ++ show tag ++ " " ++ show xs ++ ")"
      where
        showFlag : ConInfo -> String
        showFlag DATACON = ""
        showFlag f = show f ++ " "
    show (NmOp _ op xs)
        = assert_total $ "(" ++ show op ++ " " ++ show xs ++ ")"
    show (NmExtPrim _ p xs)
        = assert_total $ "(%extern " ++ show p ++ " " ++ show xs ++ ")"
    show (NmForce _ lr x) = "(%force " ++ show lr ++ " " ++ show x ++ ")"
    show (NmDelay _ lr x) = "(%delay " ++ show lr ++ " " ++ show x ++ ")"
    show (NmConCase _ sc xs def)
        = assert_total $ "(%case " ++ show sc ++ " " ++ show xs ++ " " ++ show def ++ ")"
    show (NmConstCase _ sc xs def)
        = assert_total $ "(%case " ++ show sc ++ " " ++ show xs ++ " " ++ show def ++ ")"
    show (NmPrimVal _ x) = show x
    show (NmErased _) = "___"
    show (NmCrash _ x) = "(CRASH " ++ show x ++ ")"

  export
  Show NamedConAlt where
    show (MkNConAlt x ci tag args exp)
         = "(%concase " ++ showFlag ci ++ show x ++ " " ++ show tag ++ " " ++
             show args ++ " " ++ show exp ++ ")"
      where
        showFlag : ConInfo -> String
        showFlag DATACON = ""
        showFlag f = show f ++ " "

  export
  Show NamedConstAlt where
    show (MkNConstAlt x exp)
         = "(%constcase " ++ show x ++ " " ++ show exp ++ ")"

export
data Names : List Name -> Type where
     Nil : Names []
     (::) : Name -> Names xs -> Names (x :: xs)

elem : Name -> Names xs -> Bool
elem n [] = False
elem n (x :: xs) = n == x || elem n xs

tryNext : Name -> Name
tryNext (UN n) = MN n 0
tryNext (MN n i) = MN n (1 + i)
tryNext n = MN (nameRoot n) 0

uniqueName : Name -> Names vs -> Name
uniqueName s ns =
    if s `elem` ns
       then uniqueName (tryNext s) ns
       else s

export
getLocName : (idx : Nat) -> Names vars -> (0 p : IsVar name idx vars) -> Name
getLocName Z (x :: xs) First = x
getLocName (S k) (x :: xs) (Later p) = getLocName k xs p

export
addLocs : (args : List Name) -> Names vars -> Names (args ++ vars)
addLocs [] ns = ns
addLocs (x :: xs) ns
    = let rec = addLocs xs ns in
          uniqueName x rec :: rec

conArgs : (args : List Name) -> Names (args ++ vars) -> List Name
conArgs [] ns = []
conArgs (a :: as) (n :: ns) = n :: conArgs as ns

mutual
  forgetExp : Names vars -> CExp vars -> NamedCExp
  forgetExp locs (CLocal fc p) = NmLocal fc (getLocName _ locs p)
  forgetExp locs (CRef fc n) = NmRef fc n
  forgetExp locs (CLam fc x sc)
      = let locs' = addLocs [x] locs in
            NmLam fc (getLocName _ locs' First) (forgetExp locs' sc)
  forgetExp locs (CLet fc x _ val sc)
      = let locs' = addLocs [x] locs in
            NmLet fc (getLocName _ locs' First)
                     (forgetExp locs val)
                     (forgetExp locs' sc)
  forgetExp locs (CApp fc f args)
      = NmApp fc (forgetExp locs f) (map (forgetExp locs) args)
  forgetExp locs (CCon fc n ci t args)
      = NmCon fc n ci t (map (forgetExp locs) args)
  forgetExp locs (COp fc op args)
      = NmOp fc op (map (forgetExp locs) args)
  forgetExp locs (CExtPrim fc p args)
      = NmExtPrim fc p (map (forgetExp locs) args)
  forgetExp locs (CForce fc lr f)
      = NmForce fc lr (forgetExp locs f)
  forgetExp locs (CDelay fc lr f)
      = NmDelay fc lr (forgetExp locs f)
  forgetExp locs (CConCase fc sc alts def)
      = NmConCase fc (forgetExp locs sc) (map (forgetConAlt locs) alts)
                     (map (forgetExp locs) def)
  forgetExp locs (CConstCase fc sc alts def)
      = NmConstCase fc (forgetExp locs sc) (map (forgetConstAlt locs) alts)
                       (map (forgetExp locs) def)
  forgetExp locs (CPrimVal fc c) = NmPrimVal fc c
  forgetExp locs (CErased fc) = NmErased fc
  forgetExp locs (CCrash fc msg) = NmCrash fc msg

  forgetConAlt : Names vars -> CConAlt vars -> NamedConAlt
  forgetConAlt locs (MkConAlt n ci t args exp)
      = let args' = addLocs args locs in
            MkNConAlt n ci t (conArgs args args') (forgetExp args' exp)

  forgetConstAlt : Names vars -> CConstAlt vars -> NamedConstAlt
  forgetConstAlt locs (MkConstAlt c exp)
      = MkNConstAlt c (forgetExp locs exp)

export
forget : {vars : _} -> CExp vars -> NamedCExp
forget {vars} exp
    = forgetExp (addLocs vars [])
                (rewrite appendNilRightNeutral vars in exp)

export
forgetDef : CDef -> NamedDef
forgetDef (MkFun args def)
    = let ns = addLocs args []
          args' = conArgs {vars = []} args ns in
          MkNmFun args' (forget def)
forgetDef (MkCon t a nt) = MkNmCon t a nt
forgetDef (MkForeign ccs fargs ty) = MkNmForeign ccs fargs ty
forgetDef (MkError err) = MkNmError (forget err)

export
{vars : _} -> Show (CExp vars) where
  show exp = show (forget exp)

export
Show CFType where
  show CFUnit = "Unit"
  show CFInt = "Int"
  show CFInt8 = "Int_8"
  show CFInt16 = "Int_16"
  show CFInt32 = "Int_32"
  show CFInt64 = "Int_64"
  show CFUnsigned8 = "Bits_8"
  show CFUnsigned16 = "Bits_16"
  show CFUnsigned32 = "Bits_32"
  show CFUnsigned64 = "Bits_64"
  show CFString = "String"
  show CFDouble = "Double"
  show CFChar = "Char"
  show CFPtr = "Ptr"
  show CFGCPtr = "GCPtr"
  show CFBuffer = "Buffer"
  show CFWorld = "%World"
  show (CFFun s t) = show s ++ " -> " ++ show t
  show (CFIORes t) = "IORes " ++ show t
  show (CFStruct n args) = "struct " ++ show n ++ " " ++ showSep " " (map show args)
  show (CFUser n args) = show n ++ " " ++ showSep " " (map show args)

export
Show CDef where
  show (MkFun args exp) = show args ++ ": " ++ show exp
  show (MkCon tag arity pos)
      = "Constructor tag " ++ show tag ++ " arity " ++ show arity ++
        maybe "" (\n => " (newtype by " ++ show n ++ ")") pos
  show (MkForeign ccs args ret)
      = "Foreign call " ++ show ccs ++ " " ++
        show args ++ " -> " ++ show ret
  show (MkError exp) = "Error: " ++ show exp

export
Show NamedDef where
  show (MkNmFun args exp) = show args ++ ": " ++ show exp
  show (MkNmCon tag arity pos)
      = "Constructor tag " ++ show tag ++ " arity " ++ show arity ++
        maybe "" (\n => " (newtype by " ++ show n ++ ")") pos
  show (MkNmForeign ccs args ret)
      = "Foreign call " ++ show ccs ++ " " ++
        show args ++ " -> " ++ show ret
  show (MkNmError exp) = "Error: " ++ show exp

mutual
  export
  insertNames : SizeOf outer ->
                SizeOf ns ->
                CExp (outer ++ inner) ->
                CExp (outer ++ (ns ++ inner))
  insertNames outer ns (CLocal fc prf)
      = let MkNVar var' = insertNVarNames outer ns (MkNVar prf) in
            CLocal fc var'
  insertNames _ _ (CRef fc x) = CRef fc x
  insertNames outer ns (CLam fc x sc)
      = let sc' = insertNames (suc outer) ns sc in
            CLam fc x sc'
  insertNames outer ns (CLet fc x inl val sc)
      = let sc' = insertNames (suc outer) ns sc in
            CLet fc x inl (insertNames outer ns val) sc'
  insertNames outer ns (CApp fc x xs)
      = CApp fc (insertNames outer ns x) (assert_total (map (insertNames outer ns) xs))
  insertNames outer ns (CCon fc ci x tag xs)
      = CCon fc ci x tag (assert_total (map (insertNames outer ns) xs))
  insertNames outer ns (COp fc x xs)
      = COp fc x (assert_total (map (insertNames outer ns) xs))
  insertNames outer ns (CExtPrim fc p xs)
      = CExtPrim fc p (assert_total (map (insertNames outer ns) xs))
  insertNames outer ns (CForce fc lr x) = CForce fc lr (insertNames outer ns x)
  insertNames outer ns (CDelay fc lr x) = CDelay fc lr (insertNames outer ns x)
  insertNames outer ns (CConCase fc sc xs def)
      = CConCase fc (insertNames outer ns sc) (assert_total (map (insertNamesConAlt outer ns) xs))
                 (assert_total (map (insertNames outer ns) def))
  insertNames outer ns (CConstCase fc sc xs def)
      = CConstCase fc (insertNames outer ns sc) (assert_total (map (insertNamesConstAlt outer ns) xs))
                   (assert_total (map (insertNames outer ns) def))
  insertNames _ _ (CPrimVal fc x) = CPrimVal fc x
  insertNames _ _ (CErased fc) = CErased fc
  insertNames _ _ (CCrash fc x) = CCrash fc x

  insertNamesConAlt : SizeOf outer ->
                      SizeOf ns ->
                      CConAlt (outer ++ inner) ->
                      CConAlt (outer ++ (ns ++ inner))
  insertNamesConAlt {outer} {ns} p q (MkConAlt x ci tag args sc)
        = let sc' : CExp ((args ++ outer) ++ inner)
                  = rewrite sym (appendAssociative args outer inner) in sc in
              MkConAlt x ci tag args
               (rewrite appendAssociative args outer (ns ++ inner) in
                        insertNames (mkSizeOf args + p) q sc')

  insertNamesConstAlt : SizeOf outer ->
                        SizeOf ns ->
                        CConstAlt (outer ++ inner) ->
                        CConstAlt (outer ++ (ns ++ inner))
  insertNamesConstAlt outer ns (MkConstAlt x sc) = MkConstAlt x (insertNames outer ns sc)

mutual
  export
  embed : CExp args -> CExp (args ++ vars)
  embed cexp = believe_me cexp
  -- It is identity at run time, but it would be implemented as below
  -- (not sure theere's much performance benefit, mind...)
  {-
  embed (CLocal fc prf) = CLocal fc (varExtend prf)
  embed (CRef fc n) = CRef fc n
  embed (CLam fc x sc) = CLam fc x (embed sc)
  embed (CLet fc x inl val sc) = CLet fc x inl (embed val) (embed sc)
  embed (CApp fc f args) = CApp fc (embed f) (assert_total (map embed args))
  embed (CCon fc n t args) = CCon fc n t (assert_total (map embed args))
  embed (COp fc p args) = COp fc p (assert_total (map embed args))
  embed (CExtPrim fc p args) = CExtPrim fc p (assert_total (map embed args))
  embed (CForce fc e) = CForce fc (embed e)
  embed (CDelay fc e) = CDelay fc (embed e)
  embed (CConCase fc sc alts def)
      = CConCase fc (embed sc) (assert_total (map embedAlt alts))
                 (assert_total (map embed def))
  embed (CConstCase fc sc alts def)
      = CConstCase fc (embed sc) (assert_total (map embedConstAlt alts))
                   (assert_total (map embed def))
  embed (CPrimVal fc c) = CPrimVal fc c
  embed (CErased fc) = CErased fc
  embed (CCrash fc msg) = CCrash fc msg

  embedAlt : CConAlt args -> CConAlt (args ++ vars)
  embedAlt {args} {vars} (MkConAlt n t as sc)
     = MkConAlt n t as (rewrite appendAssociative as args vars in embed sc)

  embedConstAlt : CConstAlt args -> CConstAlt (args ++ vars)
  embedConstAlt (MkConstAlt c sc) = MkConstAlt c (embed sc)
  -}

mutual
  -- Shrink the scope of a compiled expression, replacing any variables not
  -- in the remaining set with Erased
  export
  shrinkCExp : SubVars newvars vars -> CExp vars -> CExp newvars
  shrinkCExp sub (CLocal fc prf)
      = case subElem prf sub of
             Nothing => CErased fc
             Just (MkVar prf') => CLocal fc prf'
  shrinkCExp _ (CRef fc x) = CRef fc x
  shrinkCExp sub (CLam fc x sc)
      = let sc' = shrinkCExp (KeepCons sub) sc in
            CLam fc x sc'
  shrinkCExp sub (CLet fc x inl val sc)
      = let sc' = shrinkCExp (KeepCons sub) sc in
            CLet fc x inl (shrinkCExp sub val) sc'
  shrinkCExp sub (CApp fc x xs)
      = CApp fc (shrinkCExp sub x) (assert_total (map (shrinkCExp sub) xs))
  shrinkCExp sub (CCon fc x ci tag xs)
      = CCon fc x ci tag (assert_total (map (shrinkCExp sub) xs))
  shrinkCExp sub (COp fc x xs)
      = COp fc x (assert_total (map (shrinkCExp sub) xs))
  shrinkCExp sub (CExtPrim fc p xs)
      = CExtPrim fc p (assert_total (map (shrinkCExp sub) xs))
  shrinkCExp sub (CForce fc lr x) = CForce fc lr (shrinkCExp sub x)
  shrinkCExp sub (CDelay fc lr x) = CDelay fc lr (shrinkCExp sub x)
  shrinkCExp sub (CConCase fc sc xs def)
      = CConCase fc (shrinkCExp sub sc)
                 (assert_total (map (shrinkConAlt sub) xs))
                 (assert_total (map (shrinkCExp sub) def))
  shrinkCExp sub (CConstCase fc sc xs def)
      = CConstCase fc (shrinkCExp sub sc)
                   (assert_total (map (shrinkConstAlt sub) xs))
                   (assert_total (map (shrinkCExp sub) def))
  shrinkCExp _ (CPrimVal fc x) = CPrimVal fc x
  shrinkCExp _ (CErased fc) = CErased fc
  shrinkCExp _ (CCrash fc x) = CCrash fc x

  shrinkConAlt : SubVars newvars vars -> CConAlt vars -> CConAlt newvars
  shrinkConAlt sub (MkConAlt x ci tag args sc)
        = MkConAlt x ci tag args (shrinkCExp (subExtend args sub) sc)

  shrinkConstAlt : SubVars newvars vars -> CConstAlt vars -> CConstAlt newvars
  shrinkConstAlt sub (MkConstAlt x sc) = MkConstAlt x (shrinkCExp sub sc)

export
Weaken CExp where
  weakenNs ns tm = insertNames zero ns tm

export
Weaken CConAlt where
  weakenNs ns tm = insertNamesConAlt zero ns tm

-- Substitute some explicit terms for names in a term, and remove those
-- names from the scope
namespace SubstCEnv
  public export
  data SubstCEnv : List Name -> List Name -> Type where
       Nil : SubstCEnv [] vars
       (::) : CExp vars ->
              SubstCEnv ds vars -> SubstCEnv (d :: ds) vars

findDrop : FC -> Var (dropped ++ vars) ->
           SubstCEnv dropped vars -> CExp vars
findDrop fc (MkVar p) [] = CLocal fc p
findDrop fc (MkVar First) (tm :: env) = tm
findDrop fc (MkVar (Later p)) (tm :: env) = findDrop fc (MkVar p) env

find : FC ->
       SizeOf outer ->
       Var (outer ++ (dropped ++ vars)) ->
       SubstCEnv dropped vars ->
       CExp (outer ++ vars)
find fc outer var env = case sizedView outer of
  Z       => findDrop fc var env
  S outer => case var of
    MkVar First     => CLocal fc First
    MkVar (Later p) => weaken (find fc outer (MkVar p) env)
    -- TODO: refactor to weaken only once?

mutual
  substEnv : SizeOf outer ->
             SubstCEnv dropped vars ->
             CExp (outer ++ (dropped ++ vars)) ->
             CExp (outer ++ vars)
  substEnv outer env (CLocal fc prf)
      = find fc outer (MkVar prf) env
  substEnv _ _ (CRef fc x) = CRef fc x
  substEnv outer env (CLam fc x sc)
      = let sc' = substEnv (suc outer) env sc in
            CLam fc x sc'
  substEnv outer env (CLet fc x inl val sc)
      = let sc' = substEnv (suc outer) env sc in
            CLet fc x inl (substEnv outer env val) sc'
  substEnv outer env (CApp fc x xs)
      = CApp fc (substEnv outer env x) (assert_total (map (substEnv outer env) xs))
  substEnv outer env (CCon fc x ci tag xs)
      = CCon fc x ci tag (assert_total (map (substEnv outer env) xs))
  substEnv outer env (COp fc x xs)
      = COp fc x (assert_total (map (substEnv outer env) xs))
  substEnv outer env (CExtPrim fc p xs)
      = CExtPrim fc p (assert_total (map (substEnv outer env) xs))
  substEnv outer env (CForce fc lr x) = CForce fc lr (substEnv outer env x)
  substEnv outer env (CDelay fc lr x) = CDelay fc lr (substEnv outer env x)
  substEnv outer env (CConCase fc sc xs def)
      = CConCase fc (substEnv outer env sc)
                 (assert_total (map (substConAlt outer env) xs))
                 (assert_total (map (substEnv outer env) def))
  substEnv outer env (CConstCase fc sc xs def)
      = CConstCase fc (substEnv outer env sc)
                   (assert_total (map (substConstAlt outer env) xs))
                   (assert_total (map (substEnv outer env) def))
  substEnv _ _ (CPrimVal fc x) = CPrimVal fc x
  substEnv _ _ (CErased fc) = CErased fc
  substEnv _ _ (CCrash fc x) = CCrash fc x

  substConAlt : SizeOf outer ->
                SubstCEnv dropped vars ->
                CConAlt (outer ++ (dropped ++ vars)) ->
                CConAlt (outer ++ vars)
  substConAlt {vars} {outer} {dropped} p env (MkConAlt x ci tag args sc)
      = MkConAlt x ci tag args
           (rewrite appendAssociative args outer vars in
                    substEnv (mkSizeOf args + p) env
                      (rewrite sym (appendAssociative args outer (dropped ++ vars)) in
                               sc))

  substConstAlt : SizeOf outer ->
                  SubstCEnv dropped vars ->
                  CConstAlt (outer ++ (dropped ++ vars)) ->
                  CConstAlt (outer ++ vars)
  substConstAlt outer env (MkConstAlt x sc) = MkConstAlt x (substEnv outer env sc)

export
substs : {dropped, vars : _} ->
         SubstCEnv dropped vars -> CExp (dropped ++ vars) -> CExp vars
substs env tm = substEnv zero env tm

resolveRef : SizeOf outer ->
             SizeOf done ->
             Bounds bound -> FC -> Name ->
             Maybe (CExp (outer ++ (done ++ bound ++ vars)))
resolveRef _ _ None _ _ = Nothing
resolveRef {outer} {vars} {done} p q (Add {xs} new old bs) fc n
    = if n == old
         then rewrite appendAssociative outer done (new :: xs ++ vars) in
              let MkNVar p = weakenNVar (p + q) (MkNVar First) in
                    Just (CLocal fc p)
         else rewrite appendAssociative done [new] (xs ++ vars)
                in resolveRef p (sucR q) bs fc n

mutual
  export
  mkLocals : SizeOf outer ->
             Bounds bound ->
             CExp (outer ++ vars) ->
             CExp (outer ++ (bound ++ vars))
  mkLocals later bs (CLocal {idx} {x} fc p)
      = let MkNVar p' = addVars later bs (MkNVar p) in CLocal {x} fc p'
  mkLocals later bs (CRef fc var)
      = maybe (CRef fc var) id (resolveRef later zero bs fc var)
  mkLocals later bs (CLam fc x sc)
      = let sc' = mkLocals (suc later) bs sc in
            CLam fc x sc'
  mkLocals later bs (CLet fc x inl val sc)
      = let sc' = mkLocals (suc later) bs sc in
            CLet fc x inl (mkLocals later bs val) sc'
  mkLocals later bs (CApp fc f xs)
      = CApp fc (mkLocals later bs f) (assert_total (map (mkLocals later bs) xs))
  mkLocals later bs (CCon fc ci x tag xs)
      = CCon fc ci x tag (assert_total (map (mkLocals later bs) xs))
  mkLocals later bs (COp fc x xs)
      = COp fc x (assert_total (map (mkLocals later bs) xs))
  mkLocals later bs (CExtPrim fc x xs)
      = CExtPrim fc x (assert_total (map (mkLocals later bs) xs))
  mkLocals later bs (CForce fc lr x)
      = CForce fc lr (mkLocals later bs x)
  mkLocals later bs (CDelay fc lr x)
      = CDelay fc lr (mkLocals later bs x)
  mkLocals later bs (CConCase fc sc xs def)
      = CConCase fc (mkLocals later bs sc)
                 (assert_total (map (mkLocalsConAlt later bs) xs))
                 (assert_total (map (mkLocals later bs) def))
  mkLocals later bs (CConstCase fc sc xs def)
      = CConstCase fc (mkLocals later bs sc)
                 (assert_total (map (mkLocalsConstAlt later bs) xs))
                 (assert_total (map (mkLocals later bs) def))
  mkLocals later bs (CPrimVal fc x) = CPrimVal fc x
  mkLocals later bs (CErased fc) = CErased fc
  mkLocals later bs (CCrash fc x) = CCrash fc x

  mkLocalsConAlt : SizeOf outer ->
                   Bounds bound ->
                   CConAlt (outer ++ vars) ->
                   CConAlt (outer ++ (bound ++ vars))
  mkLocalsConAlt {bound} {outer} {vars} p bs (MkConAlt x ci tag args sc)
        = let sc' : CExp ((args ++ outer) ++ vars)
                  = rewrite sym (appendAssociative args outer vars) in sc in
              MkConAlt x ci tag args
               (rewrite appendAssociative args outer (bound ++ vars) in
                        mkLocals (mkSizeOf args + p) bs sc')

  mkLocalsConstAlt : SizeOf outer ->
                     Bounds bound ->
                     CConstAlt (outer ++ vars) ->
                     CConstAlt (outer ++ (bound ++ vars))
  mkLocalsConstAlt later bs (MkConstAlt x sc) = MkConstAlt x (mkLocals later bs sc)

export
refsToLocals : Bounds bound -> CExp vars -> CExp (bound ++ vars)
refsToLocals None tm = tm
refsToLocals bs y = mkLocals zero bs y

export
getFC : CExp args -> FC
getFC (CLocal fc _) = fc
getFC (CRef fc _) = fc
getFC (CLam fc _ _) = fc
getFC (CLet fc _ _ _ _) = fc
getFC (CApp fc _ _) = fc
getFC (CCon fc _ _ _ _) = fc
getFC (COp fc _ _) = fc
getFC (CExtPrim fc _ _) = fc
getFC (CForce fc _ _) = fc
getFC (CDelay fc _ _) = fc
getFC (CConCase fc _ _ _) = fc
getFC (CConstCase fc _ _ _) = fc
getFC (CPrimVal fc _) = fc
getFC (CErased fc) = fc
getFC (CCrash fc _) = fc

namespace NamedCExp
  export
  getFC : NamedCExp -> FC
  getFC (NmLocal fc _) = fc
  getFC (NmRef fc _) = fc
  getFC (NmLam fc _ _) = fc
  getFC (NmLet fc _ _ _) = fc
  getFC (NmApp fc _ _) = fc
  getFC (NmCon fc _ _ _ _) = fc
  getFC (NmOp fc _ _) = fc
  getFC (NmExtPrim fc _ _) = fc
  getFC (NmForce fc _ _) = fc
  getFC (NmDelay fc _ _) = fc
  getFC (NmConCase fc _ _ _) = fc
  getFC (NmConstCase fc _ _ _) = fc
  getFC (NmPrimVal fc _) = fc
  getFC (NmErased fc) = fc
  getFC (NmCrash fc _) = fc
