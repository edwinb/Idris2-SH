module Compiler.Scheme.Gambit

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Generated
import Compiler.Inline
import Compiler.Scheme.Common

import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT
import Libraries.Utils.Hex
import Libraries.Utils.Path

import Data.List
import Data.Maybe
import Libraries.Data.NameMap
import Data.String
import Data.Vect

import Idris.Env

import System
import System.Directory
import System.File
import System.Info

%default covering

-- TODO Look for gsi-script, then gsi
findGSI : IO String
findGSI =
  do env <- idrisGetEnv "GAMBIT_GSI"
     pure $ fromMaybe "/usr/bin/env gsi" env

-- TODO Look for gsc-script, then gsc
findGSC : IO String
findGSC =
  do env <- idrisGetEnv "GAMBIT_GSC"
     pure $ fromMaybe "/usr/bin/env gsc" env

findGSCBackend : IO String
findGSCBackend =
  do env <- idrisGetEnv "GAMBIT_GSC_BACKEND"
     pure $ case env of
              Nothing => ""
              Just e => " -cc " ++ e

schHeader : String
schHeader =
    "; " ++ (generatedString "Gambit") ++ "\n" ++
    "(declare (block)\n" ++
    "(inlining-limit 450)\n" ++
    "(standard-bindings)\n" ++
    "(extended-bindings)\n" ++
    "(not safe)\n" ++
    "(optimize-dead-definitions))\n"

showGambitChar : Char -> String -> String
showGambitChar '\\' = ("\\\\" ++)
showGambitChar c
   = if c < chr 32 -- XXX
        then (("\\x" ++ asHex (cast c) ++ ";") ++)
        else strCons c

showGambitString : List Char -> String -> String
showGambitString [] = id
showGambitString ('"'::cs) = ("\\\"" ++) . showGambitString cs
showGambitString (c::cs) = (showGambitChar c) . showGambitString cs

gambitString : String -> String
gambitString cs = strCons '"' (showGambitString (unpack cs) "\"")

mutual
  handleRet : String -> String -> String
  handleRet "void" op = op ++ " " ++ mkWorld (schConstructor 0 [])
  handleRet _ op = mkWorld op

  getFArgs : NamedCExp -> Core (List (NamedCExp, NamedCExp))
  getFArgs (NmCon fc _ _ 0 _) = pure []
  getFArgs (NmCon fc _ _ 1 [ty, val, rest]) = pure $ (ty, val) :: !(getFArgs rest)
  getFArgs arg = throw (GenericMsg (getFC arg) ("Badly formed c call argument list " ++ show arg))

  gambitPrim : Int -> ExtPrim -> List NamedCExp -> Core String
  gambitPrim i GetField [NmPrimVal _ (Str s), _, _, struct,
                         NmPrimVal _ (Str fld), _]
      = do structsc <- schExp gambitPrim gambitString 0 struct
           pure $ "(" ++ s ++ "-" ++ fld ++ " " ++ structsc ++ ")"
  gambitPrim i GetField [_,_,_,_,_,_]
      = pure "(error \"bad getField\")"
  gambitPrim i SetField [NmPrimVal _ (Str s), _, _, struct,
                         NmPrimVal _ (Str fld), _, val, world]
      = do structsc <- schExp gambitPrim gambitString 0 struct
           valsc <- schExp gambitPrim gambitString 0 val
           pure $ mkWorld $
                "(" ++ s ++ "-" ++ fld ++ "-set! " ++ structsc ++ " " ++ valsc ++ ")"
  gambitPrim i SetField [_,_,_,_,_,_,_,_]
      = pure "(error \"bad setField\")"
  gambitPrim i SysCodegen []
      = pure $ "\"gambit\""
  gambitPrim i prim args
      = schExtCommon gambitPrim gambitString i prim args

-- Reference label for keeping track of loaded external libraries
data Loaded : Type where

-- Label for noting which struct types are declared
data Structs : Type where

notWorld : CFType -> Bool
notWorld CFWorld = False
notWorld _ = True

cType : FC -> CFType -> Core String
cType fc CFUnit = pure "void"
cType fc CFInt = pure "int"
cType fc CFString = pure "char *"
cType fc CFDouble = pure "double"
cType fc CFChar = pure "char"
cType fc CFPtr = pure "void *"
cType fc (CFIORes t) = cType fc t
cType fc (CFStruct n t) = pure $ "struct " ++ n
cType fc (CFFun s t) = funTySpec [s] t
  where
    funTySpec : List CFType -> CFType -> Core String
    funTySpec args (CFFun CFWorld t) = funTySpec args t
    funTySpec args (CFFun s t) = funTySpec (s :: args) t
    funTySpec args retty
        = do rtyspec <- cType fc retty
             argspecs <- traverse (cType fc) (reverse . filter notWorld $ args)
             pure $ rtyspec ++ " (*)(" ++ showSep ", " argspecs ++ ")"
cType fc t = throw (GenericMsg fc ("Can't pass argument of type " ++ show t ++
                       " to foreign function"))

cftySpec : FC -> CFType -> Core String
cftySpec fc CFUnit = pure "void"
cftySpec fc CFInt = pure "int"
cftySpec fc CFInt8 = pure "char"
cftySpec fc CFInt16 = pure "short"
cftySpec fc CFInt32 = pure "int"
cftySpec fc CFInt64 = pure "long"
cftySpec fc CFUnsigned8 = pure "unsigned-char"
cftySpec fc CFUnsigned16 = pure "unsigned-short"
cftySpec fc CFUnsigned32 = pure "unsigned-int"
cftySpec fc CFUnsigned64 = pure "unsigned-long"
cftySpec fc CFString = pure "UTF-8-string"
cftySpec fc CFDouble = pure "double"
cftySpec fc CFChar = pure "char"
cftySpec fc CFPtr = pure "(pointer void)"
cftySpec fc (CFIORes t) = cftySpec fc t
cftySpec fc (CFStruct n t) = pure $ n ++ "*/nonnull"
cftySpec fc (CFFun s t) = funTySpec [s] t
  where
    funTySpec : List CFType -> CFType -> Core String
    funTySpec args (CFFun CFWorld t) = funTySpec args t
    funTySpec args (CFFun s t) = funTySpec (s :: args) t
    funTySpec args retty
        = do rtyspec <- cftySpec fc retty
             argspecs <- traverse (cftySpec fc) (reverse . filter notWorld $ args)
             pure $ "(function (" ++ showSep " " argspecs ++ ") " ++ rtyspec ++ ")"
cftySpec fc t = throw (GenericMsg fc ("Can't pass argument of type " ++ show t ++
                         " to foreign function"))


record CCallbackInfo where
  constructor MkCCallbackInfo
  schemeArgName : String
  schemeWrapName : String
  callbackBody : String
  argTypes : List String
  retType : String

record CWrapperDefs where
  constructor MkCWrapperDefs
  setBox : String
  boxDef : String
  cWrapDef : String

cCall : {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        FC -> (cfn : String) -> (fnWrapName : String -> String) -> (clib : String) ->
        List (Name, CFType) -> CFType -> Core (String, String)
cCall fc cfn fnWrapName clib args ret
    = do -- loaded <- get Loaded
         -- lib <- if clib `elem` loaded
         --           then pure ""
         --           else do (fname, fullname) <- locate clib
         --                   copyLib (fname, fullname)
         --                   put Loaded (clib :: loaded)
         --                   pure ""
         argTypes <- traverse (cftySpec fc . snd) args
         retType <- cftySpec fc ret

         argsInfo <- traverse buildArg args
         argCTypes <- traverse (cType fc . snd) args
         retCType <- cType fc ret

         let cWrapperDefs = map buildCWrapperDefs $ mapMaybe snd argsInfo
         let cFunWrapDeclaration = buildCFunWrapDeclaration cfn retCType argCTypes
         let wrapDeclarations = cFunWrapDeclaration
                                ++ concatMap (.boxDef) cWrapperDefs
                                ++ concatMap (.cWrapDef) cWrapperDefs

         let setBoxes = concatMap (.setBox) cWrapperDefs
         let call = " ((c-lambda (" ++ showSep " " argTypes ++ ") "
                      ++ retType ++ " " ++ show cfn ++ ") "
                      ++ showSep " " (map fst argsInfo) ++ ")"
         let body = setBoxes ++ "\n" ++ call

         pure $ case ret of -- XXX
                     CFIORes _ => (handleRet retType body, wrapDeclarations)
                     _ => (body, wrapDeclarations)
  where
    mkNs : Int -> List CFType -> List (Maybe String)
    mkNs i [] = []
    mkNs i (CFWorld :: xs) = Nothing :: mkNs i xs
    mkNs i (x :: xs) = Just ("cb" ++ show i) :: mkNs (i + 1) xs

    applyLams : String -> List (Maybe String) -> String
    applyLams n [] = n
    applyLams n (Nothing :: as) = applyLams ("(" ++ n ++ " #f)") as
    applyLams n (Just a :: as) = applyLams ("(" ++ n ++ " " ++ a ++ ")") as

    replaceChar : Char -> Char -> String -> String
    replaceChar old new = pack . replaceOn old new . unpack

    buildCWrapperDefs : CCallbackInfo -> CWrapperDefs
    buildCWrapperDefs (MkCCallbackInfo arg schemeWrap callbackStr argTypes retType) =
      let box = schemeWrap ++ "-box"
          setBox = "\n (set-box! " ++ box ++ " " ++ callbackStr ++ ")"
          cWrapName = replaceChar '-' '_' schemeWrap
          boxDef = "\n(define " ++ box ++ " (box #f))\n"

          args =
            if length argTypes > 0
              then " " ++ (showSep " " $ map (\i => "farg-" ++ show i) [0 .. (natToInteger $ length argTypes) - 1])
              else ""

          cWrapDef =
            "\n(c-define " ++
            "(" ++ schemeWrap ++ args ++ ")" ++
            " (" ++ showSep " " argTypes ++ ")" ++
            " " ++ retType ++
            " \"" ++ cWrapName ++ "\"" ++ " \"\"" ++
            "\n ((unbox " ++ box ++ ")" ++ args ++ ")" ++
            "\n)\n"
      in MkCWrapperDefs setBox boxDef cWrapDef

    buildCFunWrapDeclaration : String -> String -> List String -> String
    buildCFunWrapDeclaration name ret args =
      "\n(c-declare #<<c-declare-end\n" ++
      ret ++ " " ++ name ++ "(" ++ showSep ", " args ++ ");" ++
      "\nc-declare-end\n)\n"

    mkFun : List CFType -> CFType -> String -> String
    mkFun args ret n
        = let argns = mkNs 0 args in
              "(lambda (" ++ showSep " " (mapMaybe id argns) ++ ") "
              ++ (applyLams n argns ++ ")")

    callback : String -> List CFType -> CFType -> Core (String, List String, String)
    callback n args (CFFun s t) = callback n (s :: args) t
    callback n args_rev retty
        = do let args = reverse args_rev
             argTypes <- traverse (cftySpec fc) (filter notWorld args)
             retType <- cftySpec fc retty
             pure (mkFun args retty n, argTypes, retType)

    buildArg : (Name, CFType) -> Core (String, Maybe CCallbackInfo)
    buildArg (n, CFFun s t) = do
      let arg = schName n
      let schemeWrap = fnWrapName arg
      (callbackBody, argTypes, retType) <- callback arg [s] t
      pure (schemeWrap, Just $ MkCCallbackInfo arg schemeWrap callbackBody argTypes retType)
    buildArg (n, _) = pure (schName n, Nothing)

schemeCall : FC -> (sfn : String) ->
             List Name -> CFType -> Core String
schemeCall fc sfn argns ret
    = let call = "(" ++ sfn ++ " " ++ showSep " " (map schName argns) ++ ")" in
          case ret of
               CFIORes _ => pure $ mkWorld call
               _ => pure call

-- Use a calling convention to compile a foreign def.
-- Returns the name of the static library to link and the body
-- of the function call.
useCC : {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        FC -> List String -> List (Name, CFType) -> CFType -> Core (Maybe String, (String, String))
useCC fc ccs args ret
    = case parseCC ["scheme,gambit", "scheme", "C"] ccs of
           Nothing => throw (NoForeignCC fc ccs)
           Just ("scheme,gambit", [sfn]) => pure (Nothing, (!(schemeCall fc sfn (map fst args) ret), ""))
           Just ("scheme", [sfn]) => pure (Nothing, (!(schemeCall fc sfn (map fst args) ret), ""))
           Just ("C", [cfn, clib]) => pure (Just clib, !(cCall fc cfn (fnWrapName cfn) clib args ret))
           Just ("C", [cfn, clib, chdr]) => pure (Just clib, !(cCall fc cfn (fnWrapName cfn) clib args ret))
           _ => throw (NoForeignCC fc ccs)
  where
    fnWrapName : String -> String -> String
    fnWrapName cfn schemeArgName = schemeArgName ++ "-" ++ cfn ++ "-cFunWrap"


-- For every foreign arg type, return a name, and whether to pass it to the
-- foreign call (we don't pass '%World')
mkArgs : Int -> List CFType -> List (Name, Bool)
mkArgs i [] = []
mkArgs i (CFWorld :: cs) = (MN "farg" i, False) :: mkArgs i cs
mkArgs i (c :: cs) = (MN "farg" i, True) :: mkArgs (i + 1) cs

mkStruct : {auto s : Ref Structs (List String)} ->
           CFType -> Core String
mkStruct (CFStruct n flds)
    = do defs <- traverse mkStruct (map snd flds)
         strs <- get Structs
         if n `elem` strs
            then pure (concat defs)
            else do put Structs (n :: strs)
                    pure $ concat defs ++ "(define-c-struct " ++ n ++ " "
                           ++ showSep " " !(traverse showFld flds) ++ ")\n"
  where
    showFld : (String, CFType) -> Core String
    showFld (n, ty) = pure $ "(" ++ n ++ " " ++ !(cftySpec emptyFC ty) ++ ")"
mkStruct (CFIORes t) = mkStruct t
mkStruct (CFFun a b) = do ignore (mkStruct a); mkStruct b
mkStruct _ = pure ""

schFgnDef : {auto c : Ref Ctxt Defs} ->
            {auto l : Ref Loaded (List String)} ->
            {auto s : Ref Structs (List String)} ->
            FC -> Name -> NamedDef -> Core (Maybe String, String)
schFgnDef fc n (MkNmForeign cs args ret)
    = do let argns = mkArgs 0 args
         let allargns = map fst argns
         let useargns = map fst (filter snd argns)
         argStrs <- traverse mkStruct args
         retStr <- mkStruct ret
         (lib, (body, wrapDeclarations)) <- useCC fc cs (zip useargns args) ret
         defs <- get Ctxt
         pure (lib,
                concat argStrs ++ retStr ++
                wrapDeclarations ++
                "(define " ++ schName !(full (gamma defs) n) ++
                " (lambda (" ++ showSep " " (map schName allargns) ++ ") " ++
                body ++ "))\n")
schFgnDef _ _ _ = pure (Nothing, "")

getFgnCall : {auto c : Ref Ctxt Defs} ->
             {auto l : Ref Loaded (List String)} ->
             {auto s : Ref Structs (List String)} ->
             (Name, FC, NamedDef) -> Core (Maybe String, String)
getFgnCall (n, fc, d) = schFgnDef fc n d

compileToSCM : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core (List String)
compileToSCM c tm outfile
    = do cdata <- getCompileData False Cases tm
         let ndefs = namedDefs cdata
         -- let tags = nameTags cdata
         let ctm = forget (mainExpr cdata)

         defs <- get Ctxt
         l <- newRef {t = List String} Loaded []
         s <- newRef {t = List String} Structs []
         fgndefs <- traverse getFgnCall ndefs
         compdefs <- traverse (getScheme gambitPrim gambitString) ndefs
         let code = fastAppend (map snd fgndefs ++ compdefs)
         main <- schExp gambitPrim gambitString 0 ctm
         support <- readDataFile "gambit/support.scm"
         ds <- getDirectives Gambit
         extraRuntime <- getExtraRuntime ds
         foreign <- readDataFile "gambit/foreign.scm"
         let scm = showSep "\n" [schHeader, support, extraRuntime, foreign, code, main]
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         pure $ mapMaybe fst fgndefs

compileExpr : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c tmpDir outputDir tm outfile
    = do let srcPath = tmpDir </> outfile <.> "scm"
         let execPath = outputDir </> outfile
         libsname <- compileToSCM c tm srcPath
         libsfile <- traverse findLibraryFile $ map (<.> "a") (nub libsname)
         gsc <- coreLift findGSC
         gscBackend <- coreLift findGSCBackend
         ds <- getDirectives Gambit
         let gscCompileOpts =
             case find (== "C") ds of
                 Nothing => gscBackend ++ " -exe -cc-options \"-Wno-implicit-function-declaration\" -ld-options \"" ++
                   (showSep " " libsfile) ++ "\""
                 Just _ => " -c"
         let cmd =
             gsc ++ gscCompileOpts ++ " -o \"" ++ execPath ++ "\" \"" ++ srcPath ++ "\""
         ok <- coreLift $ system cmd
         if ok == 0
            then pure (Just execPath)
            else pure Nothing

executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm
    = do Just sh <- compileExpr c tmpDir tmpDir tm "_tmpgambit"
           | Nothing => throw (InternalError "compileExpr returned Nothing")
         coreLift_ $ system sh -- TODO: on windows, should add exe extension
         pure ()

export
codegenGambit : Codegen
codegenGambit = MkCG compileExpr executeExpr Nothing Nothing
