module Compiler.VMCode

import Compiler.ANF

import Core.CompileExpr
import Core.Context
import Core.Core
import Core.TT

import Libraries.Data.IntMap
import Data.List
import Data.Maybe
import Data.Vect

%default covering

public export
data Reg : Type where
     RVal : Reg
     Loc : Int -> Reg
     Discard : Reg

-- VM instructions - first Reg is where the result goes, unless stated
-- otherwise.

-- As long as you have a representation of closures, and an 'apply' function
-- which adds an argument and evaluates if it's fully applied, then you can
-- translate this directly to a target language program.
public export
data VMInst : Type where
     DECLARE : Reg -> VMInst
     START : VMInst -- start of the main body of the function
     ASSIGN : Reg -> Reg -> VMInst
     MKCON : Reg -> (tag : Int) -> (args : List Reg) -> VMInst
     MKCLOSURE : Reg -> Name -> (missing : Nat) -> (args : List Reg) -> VMInst
     MKCONSTANT : Reg -> Constant -> VMInst

     APPLY : Reg -> (f : Reg) -> (a : Reg) -> VMInst
     CALL : Reg -> (tailpos : Bool) -> Name -> (args : List Reg) -> VMInst
     OP : {0 arity : Nat} -> Reg -> PrimFn arity -> Vect arity Reg -> VMInst
       --  ^ we explicitly bind arity here to silence the warnings it is shadowing
       -- an existing global definition
     EXTPRIM : Reg -> Name -> List Reg -> VMInst

     CASE : Reg -> -- scrutinee
            (alts : List (Int, List VMInst)) -> -- based on constructor tag
            (def : Maybe (List VMInst)) ->
            VMInst
     CONSTCASE : Reg -> -- scrutinee
                 (alts : List (Constant, List VMInst)) ->
                 (def : Maybe (List VMInst)) ->
                 VMInst
     PROJECT : Reg -> (value : Reg) -> (pos : Int) -> VMInst
     NULL : Reg -> VMInst

     ERROR : String -> VMInst

public export
data VMDef : Type where
     MkVMFun : (args : List Int) -> List VMInst -> VMDef
     MkVMForeign : (ccs : List String) -> (fargs : List CFType) ->
                   CFType -> VMDef
     MkVMError : List VMInst -> VMDef

export
Show Reg where
  show RVal = "RVAL"
  show (Loc i) = "v" ++ show i
  show Discard = "DISCARD"

export
Show VMInst where
  show (DECLARE r) = "DECLARE " ++ show r
  show START = "START"
  show (ASSIGN r v) = show r ++ " := " ++ show v
  show (MKCON r t args)
      = show r ++ " := MKCON " ++ show t ++ " (" ++
                  showSep ", " (map show args) ++ ")"
  show (MKCLOSURE r n m args)
      = show r ++ " := MKCLOSURE " ++ show n ++ " " ++ show m ++ " (" ++
                  showSep ", " (map show args) ++ ")"
  show (MKCONSTANT r c) = show r ++ " := MKCONSTANT " ++ show c
  show (APPLY r f a) = show r ++ " := " ++ show f ++ " @ " ++ show a
  show (CALL r t n args)
      = show r ++ " := " ++ (if t then "TAILCALL " else "CALL ") ++
        show n ++ "(" ++ showSep ", " (map show args) ++ ")"
  show (OP r op args)
      = show r ++ " := " ++ "OP " ++
        show op ++ "(" ++ showSep ", " (map show (toList args)) ++ ")"
  show (EXTPRIM r n args)
      = show r ++ " := " ++ "EXTPRIM " ++
        show n ++ "(" ++ showSep ", " (map show args) ++ ")"

  show (CASE scr alts def)
      = "CASE " ++ show scr ++ " " ++ show alts ++ " {default: " ++ show def ++ "}"
  show (CONSTCASE scr alts def)
      = "CASE " ++ show scr ++ " " ++ show alts ++ " {default: " ++ show def ++ "}"

  show (PROJECT r val pos)
      = show r ++ " := PROJECT(" ++ show val ++ ", " ++ show pos ++ ")"
  show (NULL r) = show r ++ " := NULL"
  show (ERROR str) = "ERROR " ++ show str

export
Show VMDef where
  show (MkVMFun args body) = show args ++ ": " ++ show body
  show (MkVMForeign ccs args ret)
      = "Foreign call " ++ show ccs ++ " " ++
        show args ++ " " ++ show ret
  show (MkVMError err) = "Error: " ++ show err

toReg : AVar -> Reg
toReg (ALocal i) = Loc i
toReg ANull = Discard

projectArgs : Int -> Int -> (used : IntMap ()) -> (args : List Int) -> List VMInst
projectArgs scr i used [] = []
projectArgs scr i used (arg :: args)
    = case lookup arg used of
           Just _ => PROJECT (Loc arg) (Loc scr) i :: projectArgs scr (i + 1) used args
           Nothing => projectArgs scr (i + 1) used args

collectReg : Reg -> IntMap ()
collectReg (Loc i) = singleton i ()
collectReg _ = empty

collectUsed : VMInst -> IntMap ()
collectUsed (DECLARE reg) = collectReg reg
collectUsed START = empty
collectUsed (ASSIGN _ val) = collectReg val
collectUsed (MKCON _ _ args) = foldMap collectReg args
collectUsed (MKCLOSURE _ _ _ args) = foldMap collectReg args
collectUsed (MKCONSTANT _ _) = empty
collectUsed (APPLY _ fn arg) = collectReg fn <+> collectReg arg
collectUsed (CALL _ _ _ args) = foldMap collectReg args
collectUsed (OP _ _ args) = foldMap collectReg args
collectUsed (EXTPRIM _ _ args) = foldMap collectReg args
collectUsed (CASE sc is mdef)
    = collectReg sc
      <+> foldMap (foldMap collectUsed . snd) is
      <+> maybe empty (foldMap collectUsed) mdef
collectUsed (CONSTCASE sc is mdef)
    = collectReg sc
      <+> foldMap (foldMap collectUsed . snd) is
      <+> maybe empty (foldMap collectUsed) mdef
collectUsed (PROJECT _ val _) = collectReg val
collectUsed (NULL _) = empty
collectUsed (ERROR _) = empty

toVM : (tailpos : Bool) -> (target : Reg) -> ANF -> List VMInst
toVM t Discard _ = []
toVM t res (AV fc (ALocal i))
    = [ASSIGN res (Loc i)]
toVM t res (AAppName fc _ n args)
    = [CALL res t n (map toReg args)]
toVM t res (AUnderApp fc n m args)
    = [MKCLOSURE res n m (map toReg args)]
toVM t res (AApp fc _ f a)
    = [APPLY res (toReg f) (toReg a)]
toVM t res (ALet fc var val body)
    = toVM False (Loc var) val ++ toVM t res body
toVM t res (ACon fc n ci tag args)
    = [MKCON res tag (map toReg args)]
toVM t res (AOp fc _ op args)
    = [OP res op (map toReg args)]
toVM t res (AExtPrim fc _ p args)
    = [EXTPRIM res p (map toReg args)]
toVM t res (AConCase fc (ALocal scr) [MkAConAlt n ci mt args code] Nothing) -- exactly one alternative, so skip matching
    = let body = toVM t res code
          used = foldMap collectUsed body
       in projectArgs scr 0 used args ++ body
toVM t res (AConCase fc (ALocal scr) alts def)
    = [CASE (Loc scr) (map toVMConAlt alts) (map (toVM t res) def)]
  where
    toVMConAlt : AConAlt -> (Int, List VMInst)
    toVMConAlt (MkAConAlt n ci tag args code)
       = let body = toVM t res code
             used = foldMap collectUsed body
          in (tag, projectArgs scr 0 used args ++ body)
toVM t res (AConstCase fc (ALocal scr) alts def)
    = [CONSTCASE (Loc scr) (map toVMConstAlt alts) (map (toVM t res) def)]
  where
    toVMConstAlt : AConstAlt -> (Constant, List VMInst)
    toVMConstAlt (MkAConstAlt c code)
        = (c, toVM t res code)
toVM t res (APrimVal fc c)
    = [MKCONSTANT res c]
toVM t res (AErased fc)
    = [NULL res]
toVM t res (ACrash fc err)
    = [ERROR err]
toVM t res _
    = [NULL res]

findVars : VMInst -> List Int
findVars (ASSIGN (Loc r) _) = [r]
findVars (MKCON (Loc r) _ _) = [r]
findVars (MKCLOSURE (Loc r) _ _ _) = [r]
findVars (MKCONSTANT (Loc r) _) = [r]
findVars (APPLY (Loc r) _ _) = [r]
findVars (CALL (Loc r) _ _ _) = [r]
findVars (OP (Loc r) _ _) = [r]
findVars (EXTPRIM (Loc r) _ _) = [r]
findVars (CASE _ alts d)
    = foldMap findVarAlt alts ++ fromMaybe [] (map (foldMap findVars) d)
  where
    findVarAlt : (Int, List VMInst) -> List Int
    findVarAlt (t, code) = foldMap findVars code
findVars (CONSTCASE _ alts d)
    = foldMap findConstVarAlt alts ++ fromMaybe [] (map (foldMap findVars) d)
  where
    findConstVarAlt : (Constant, List VMInst) -> List Int
    findConstVarAlt (t, code) = foldMap findVars code
findVars (PROJECT (Loc r) _ _) = [r]
findVars _ = []

declareVars : List Int -> List VMInst -> List VMInst
declareVars got code
    = let vs = foldMap findVars code in
          declareAll got vs
  where
    declareAll : List Int -> List Int -> List VMInst
    declareAll got [] = START :: code
    declareAll got (i :: is)
        = if i `elem` got
             then declareAll got is
             else DECLARE (Loc i) :: declareAll (i :: got) is

export
toVMDef : ANFDef -> Maybe VMDef
toVMDef (MkAFun args body)
    = Just $ MkVMFun args (declareVars args (toVM True RVal body))
toVMDef (MkAForeign ccs cargs ret)
    = Just $ MkVMForeign ccs cargs ret
toVMDef (MkAError body)
    = Just $ MkVMError (declareVars [] (toVM True RVal body))
toVMDef _ = Nothing

export
allDefs : List (Name, ANFDef) -> List (Name, VMDef)
allDefs = mapMaybe (\ (n, d) => do d' <- toVMDef d; pure (n, d'))
