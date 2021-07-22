module Compiler.ANF

import Compiler.LambdaLift

import Core.CompileExpr
import Core.Context
import Core.Core
import Core.TT

import Data.List
import Data.Vect

%default covering

-- Convert the lambda lifted form to ANF, with variable names made explicit.
-- i.e. turn intermediate expressions into let bindings. Every argument is
-- a variable as a result.

mutual
  public export
  data AVar : Type where
       ALocal : Int -> AVar
       ANull : AVar

  public export
  data ANF : Type where
    AV : FC -> AVar -> ANF
    AAppName : FC -> (lazy : Maybe LazyReason) -> Name -> List AVar -> ANF
    AUnderApp : FC -> Name -> (missing : Nat) -> (args : List AVar) -> ANF
    AApp : FC -> (lazy : Maybe LazyReason) -> (closure : AVar) -> (arg : AVar) -> ANF
    ALet : FC -> (var : Int) -> ANF -> ANF -> ANF
    ACon : FC -> Name -> ConInfo -> (tag : Maybe Int) -> List AVar -> ANF
    AOp : {0 arity : Nat} -> FC -> (lazy : Maybe LazyReason) -> PrimFn arity -> Vect arity AVar -> ANF
        -- ^ we explicitly bind arity here to silence the warning that it shadows
        --   existing functions called arity.
    AExtPrim : FC -> (lazy : Maybe LazyReason) -> Name -> List AVar -> ANF
    AConCase : FC -> AVar -> List AConAlt -> Maybe ANF -> ANF
    AConstCase : FC -> AVar -> List AConstAlt -> Maybe ANF -> ANF
    APrimVal : FC -> Constant -> ANF
    AErased : FC -> ANF
    ACrash : FC -> String -> ANF

  public export
  data AConAlt : Type where
       MkAConAlt : Name -> ConInfo -> (tag : Maybe Int) -> (args : List Int) ->
                   ANF -> AConAlt

  public export
  data AConstAlt : Type where
       MkAConstAlt : Constant -> ANF -> AConstAlt

public export
data ANFDef : Type where
     MkAFun : (args : List Int) -> ANF -> ANFDef
     MkACon : (tag : Maybe Int) -> (arity : Nat) -> (nt : Maybe Nat) -> ANFDef
     MkAForeign : (ccs : List String) -> (fargs : List CFType) ->
                  CFType -> ANFDef
     MkAError : ANF -> ANFDef

showLazy : Maybe LazyReason -> String
showLazy = maybe "" $ (" " ++) . show

mutual
  export
  Show AVar where
    show (ALocal i) = "v" ++ show i
    show ANull = "[__]"

  export
  Show ANF where
    show (AV _ v) = show v
    show (AAppName fc lazy n args)
        = show n ++ showLazy lazy ++ "(" ++ showSep ", " (map show args) ++ ")"
    show (AUnderApp fc n m args)
        = "<" ++ show n ++ " underapp " ++ show m ++ ">(" ++
          showSep ", " (map show args) ++ ")"
    show (AApp fc lazy c arg)
        = show c ++ showLazy lazy ++ " @ (" ++ show arg ++ ")"
    show (ALet fc x val sc)
        = "%let v" ++ show x ++ " = (" ++ show val ++ ") in (" ++ show sc ++ ")"
    show (ACon fc n _ t args)
        = "%con " ++ show n ++ "(" ++ showSep ", " (map show args) ++ ")"
    show (AOp fc lazy op args)
        = "%op " ++ show op ++ showLazy lazy ++ "(" ++ showSep ", " (toList (map show args)) ++ ")"
    show (AExtPrim fc lazy p args)
        = "%extprim " ++ show p ++ showLazy lazy ++ "(" ++ showSep ", " (map show args) ++ ")"
    show (AConCase fc sc alts def)
        = "%case " ++ show sc ++ " of { "
             ++ showSep "| " (map show alts) ++ " " ++ show def ++ " }"
    show (AConstCase fc sc alts def)
        = "%case " ++ show sc ++ " of { "
             ++ showSep "| " (map show alts) ++ " " ++ show def ++ " }"
    show (APrimVal _ x) = show x
    show (AErased _) = "___"
    show (ACrash _ x) = "%CRASH(" ++ show x ++ ")"

  export
  Show AConAlt where
    show (MkAConAlt n _ t args sc)
        = "%conalt " ++ show n ++
             "(" ++ showSep ", " (map showArg args) ++ ") => " ++ show sc
      where
        showArg : Int -> String
        showArg i = "v" ++ show i

  export
  Show AConstAlt where
    show (MkAConstAlt c sc)
        = "%constalt(" ++ show c ++ ") => " ++ show sc

export
Show ANFDef where
  show (MkAFun args exp) = show args ++ ": " ++ show exp
  show (MkACon tag arity nt)
      = "Constructor tag " ++ show tag ++ " arity " ++ show arity ++ " newtype by " ++ show nt
  show (MkAForeign ccs args ret)
      = "Foreign call " ++ show ccs ++ " " ++
        show args ++ " -> " ++ show ret
  show (MkAError exp) = "Error: " ++ show exp

data AVars : List Name -> Type where
     Nil : AVars []
     (::) : Int -> AVars xs -> AVars (x :: xs)

data Next : Type where

nextVar : {auto v : Ref Next Int} ->
          Core Int
nextVar
    = do i <- get Next
         put Next (i + 1)
         pure i

lookup : {idx : _} -> (0 p : IsVar x idx vs) -> AVars vs -> Int
lookup First (x :: xs) = x
lookup (Later p) (x :: xs) = lookup p xs

bindArgs : {auto v : Ref Next Int} ->
           List ANF -> Core (List (AVar, Maybe ANF))
bindArgs [] = pure []
bindArgs (AV fc var :: xs)
    = do xs' <- bindArgs xs
         pure $ (var, Nothing) :: xs'
bindArgs (AErased fc :: xs)
    = do xs' <- bindArgs xs
         pure $ (ANull, Nothing) :: xs'
bindArgs (x :: xs)
    = do i <- nextVar
         xs' <- bindArgs xs
         pure $ (ALocal i, Just x) :: xs'

letBind : {auto v : Ref Next Int} ->
          FC -> List ANF -> (List AVar -> ANF) -> Core ANF
letBind fc args f
    = do bargs <- bindArgs args
         pure $ doBind [] bargs
  where
    doBind : List AVar -> List (AVar, Maybe ANF) -> ANF
    doBind vs [] = f (reverse vs)
    doBind vs ((ALocal i, Just t) :: xs)
        = ALet fc i t (doBind (ALocal i :: vs) xs)
    doBind vs ((var, _) :: xs) = doBind (var :: vs) xs


mlet : {auto v : Ref Next Int} ->
       FC -> ANF -> (AVar -> ANF) -> Core ANF
mlet fc (AV _ var) sc = pure $ sc var
mlet fc val sc
    = do i <- nextVar
         pure $ ALet fc i val (sc (ALocal i))

mutual
  anfArgs : {vars : _} ->
            {auto v : Ref Next Int} ->
            FC -> AVars vars ->
            List (Lifted vars) -> (List AVar -> ANF) -> Core ANF
  anfArgs fc vs args f
      = do args' <- traverse (anf vs) args
           letBind fc args' f

  anf : {vars : _} ->
        {auto v : Ref Next Int} ->
        AVars vars -> Lifted vars -> Core ANF
  anf vs (LLocal fc p) = pure $ AV fc (ALocal (lookup p vs))
  anf vs (LAppName fc lazy n args)
      = anfArgs fc vs args (AAppName fc lazy n)
  anf vs (LUnderApp fc n m args)
      = anfArgs fc vs args (AUnderApp fc n m)
  anf vs (LApp fc lazy f a)
      = anfArgs fc vs [f, a] $
                \case
                  [fvar, avar] => AApp fc lazy fvar avar
                  _ => ACrash fc "Can't happen (AApp)"
  anf vs (LLet fc x val sc)
      = do i <- nextVar
           let vs' = i :: vs
           pure $ ALet fc i !(anf vs val) !(anf vs' sc)
  anf vs (LCon fc n ci t args)
      = anfArgs fc vs args (ACon fc n ci t)
  anf vs (LOp {arity} fc lazy op args)
      = do args' <- traverse (anf vs) (toList args)
           letBind fc args'
                (\args => case toVect arity args of
                               Nothing => ACrash fc "Can't happen (AOp)"
                               Just argsv => AOp fc lazy op argsv)
  anf vs (LExtPrim fc lazy p args)
      = anfArgs fc vs args (AExtPrim fc lazy p)
  anf vs (LConCase fc scr alts def)
      = do scr' <- anf vs scr
           alts' <- traverse (anfConAlt vs) alts
           def' <- traverseOpt (anf vs) def
           mlet fc scr' (\x => AConCase fc x alts' def')
  anf vs (LConstCase fc scr alts def)
      = do scr' <- anf vs scr
           alts' <- traverse (anfConstAlt vs) alts
           def' <- traverseOpt (anf vs) def
           mlet fc scr' (\x => AConstCase fc x alts' def')
  anf vs (LPrimVal fc c) = pure $ APrimVal fc c
  anf vs (LErased fc) = pure $ AErased fc
  anf vs (LCrash fc err) = pure $ ACrash fc err

  anfConAlt : {vars : _} ->
              {auto v : Ref Next Int} ->
              AVars vars -> LiftedConAlt vars -> Core AConAlt
  anfConAlt vs (MkLConAlt n ci t args sc)
      = do (is, vs') <- bindArgs args vs
           pure $ MkAConAlt n ci t is !(anf vs' sc)
    where
      bindArgs : (args : List Name) -> AVars vars' ->
                 Core (List Int, AVars (args ++ vars'))
      bindArgs [] vs = pure ([], vs)
      bindArgs (n :: ns) vs
          = do i <- nextVar
               (is, vs') <- bindArgs ns vs
               pure (i :: is, i :: vs')

  anfConstAlt : {vars : _} ->
                {auto v : Ref Next Int} ->
                AVars vars -> LiftedConstAlt vars -> Core AConstAlt
  anfConstAlt vs (MkLConstAlt c sc)
      = pure $ MkAConstAlt c !(anf vs sc)

export
toANF : LiftedDef -> Core ANFDef
toANF (MkLFun args scope sc)
    = do v <- newRef Next (the Int 0)
         (iargs, vsNil) <- bindArgs args []
         let vs : AVars args = rewrite sym (appendNilRightNeutral args) in
                                      vsNil
         (iargs', vs) <- bindArgs scope vs
         pure $ MkAFun (iargs ++ reverse iargs') !(anf vs sc)
  where
    bindArgs : {auto v : Ref Next Int} ->
               (args : List Name) -> AVars vars' ->
               Core (List Int, AVars (args ++ vars'))
    bindArgs [] vs = pure ([], vs)
    bindArgs (n :: ns) vs
        = do i <- nextVar
             (is, vs') <- bindArgs ns vs
             pure (i :: is, i :: vs')
toANF (MkLCon t a ns) = pure $ MkACon t a ns
toANF (MkLForeign ccs fargs t) = pure $ MkAForeign ccs fargs t
toANF (MkLError err)
    = do v <- newRef Next (the Int 0)
         pure $ MkAError !(anf [] err)
