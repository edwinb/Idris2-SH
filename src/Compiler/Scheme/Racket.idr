module Compiler.Scheme.Racket

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Generated
import Compiler.Inline
import Compiler.Scheme.Common

import Core.Options
import Core.Context
import Core.Context.Log
import Core.Directory
import Core.Name
import Core.TT
import Libraries.Utils.Hex
import Libraries.Utils.Path

import Data.List
import Data.Maybe
import Libraries.Data.NameMap
import Data.Nat
import Data.String
import Data.Vect

import Idris.Env

import System
import System.Directory
import System.File
import System.Info

%default covering

findRacket : IO String
findRacket =
  do env <- idrisGetEnv "RACKET"
     pure $ fromMaybe "/usr/bin/env racket" env

findRacoExe : IO String
findRacoExe =
  do env <- idrisGetEnv "RACKET_RACO"
     pure $ (fromMaybe "/usr/bin/env raco" env) ++ " exe"

schHeader : Bool -> String -> String
schHeader prof libs
  = "#lang racket/base\n" ++
    "; " ++ (generatedString "Racket") ++ "\n" ++
    "(require racket/async-channel)\n" ++ -- for asynchronous channels
    "(require racket/future)\n" ++ -- for parallelism/concurrency
    "(require racket/math)\n" ++ -- for math ops
    "(require racket/system)\n" ++ -- for system
    "(require rnrs/bytevectors-6)\n" ++ -- for buffers
    "(require rnrs/io/ports-6)\n" ++ -- for files
    "(require srfi/19)\n" ++ -- for file handling and data
    "(require ffi/unsafe ffi/unsafe/define)\n" ++ -- for calling C
    (if prof then "(require profile)\n" else "") ++
    "(require racket/flonum)" ++ -- for float-typed transcendental functions
    libs ++
    "(let ()\n"

schFooter : String
schFooter = ") (collect-garbage)"

showRacketChar : Char -> String -> String
showRacketChar '\\' = ("\\\\" ++)
showRacketChar c
   = if c < chr 32 || c > chr 126
        then (("\\u" ++ leftPad '0' 4 (asHex (cast c))) ++)
        else strCons c

showRacketString : List Char -> String -> String
showRacketString [] = id
showRacketString ('"'::cs) = ("\\\"" ++) . showRacketString cs
showRacketString (c ::cs) = (showRacketChar c) . showRacketString cs

racketString : String -> String
racketString cs = strCons '"' (showRacketString (unpack cs) "\"")

mutual
  racketPrim : Int -> ExtPrim -> List NamedCExp -> Core String
  racketPrim i GetField [NmPrimVal _ (Str s), _, _, struct,
                         NmPrimVal _ (Str fld), _]
      = do structsc <- schExp racketPrim racketString 0 struct
           pure $ "(" ++ s ++ "-" ++ fld ++ " " ++ structsc ++ ")"
  racketPrim i GetField [_,_,_,_,_,_]
      = pure "(error \"bad getField\")"
  racketPrim i SetField [NmPrimVal _ (Str s), _, _, struct,
                         NmPrimVal _ (Str fld), _, val, world]
      = do structsc <- schExp racketPrim racketString 0 struct
           valsc <- schExp racketPrim racketString 0 val
           pure $ mkWorld $
                "(set-" ++ s ++ "-" ++ fld ++ "! " ++ structsc ++ " " ++ valsc ++ ")"
  racketPrim i SetField [_,_,_,_,_,_,_,_]
      = pure "(error \"bad setField\")"
  racketPrim i SysCodegen []
      = pure $ "\"racket\""
  racketPrim i OnCollect [_, p, c, world]
      = do p' <- schExp racketPrim racketString 0 p
           c' <- schExp racketPrim racketString 0 c
           pure $ mkWorld $ "(blodwen-register-object " ++ p' ++ " " ++ c' ++ ")"
  racketPrim i OnCollectAny [p, c, world]
      = do p' <- schExp racketPrim racketString 0 p
           c' <- schExp racketPrim racketString 0 c
           pure $ mkWorld $ "(blodwen-register-object " ++ p' ++ " " ++ c' ++ ")"
  racketPrim i MakeFuture [_, work]
      = do work' <- schExp racketPrim racketString 0 work
           pure $ mkWorld $ "(blodwen-make-future " ++ work' ++ ")"
  racketPrim i prim args
      = schExtCommon racketPrim racketString i prim args

-- Reference label for keeping track of loaded external libraries
data Loaded : Type where

-- Label for noting which struct types are declared
data Structs : Type where

-- Label for noting which foreign names are declared
data Done : Type where

cftySpec : FC -> CFType -> Core String
cftySpec fc CFUnit = pure "_void"
cftySpec fc CFInt = pure "_int"
cftySpec fc CFInt8 = pure "_int8"
cftySpec fc CFInt16 = pure "_int16"
cftySpec fc CFInt32 = pure "_int32"
cftySpec fc CFInt64 = pure "_int64"
cftySpec fc CFUnsigned8 = pure "_uint8"
cftySpec fc CFUnsigned16 = pure "_uint16"
cftySpec fc CFUnsigned32 = pure "_uint32"
cftySpec fc CFUnsigned64 = pure "_uint64"
cftySpec fc CFString = pure "_string/utf-8"
cftySpec fc CFDouble = pure "_double"
cftySpec fc CFChar = pure "_int8"
cftySpec fc CFPtr = pure "_pointer"
cftySpec fc CFGCPtr = pure "_pointer"
cftySpec fc CFBuffer = pure "_bytes"
cftySpec fc (CFIORes t) = cftySpec fc t
cftySpec fc (CFStruct n t) = pure $ "_" ++ n ++ "-pointer"
cftySpec fc (CFFun s t) = funTySpec [s] t
  where
    funTySpec : List CFType -> CFType -> Core String
    funTySpec args (CFFun CFWorld t) = funTySpec args t
    funTySpec args (CFFun s t) = funTySpec (s :: args) t
    funTySpec args retty
        = do rtyspec <- cftySpec fc retty
             argspecs <- traverse (cftySpec fc) (reverse args)
             pure $ "(_fun " ++ showSep " " argspecs ++ " -> " ++ rtyspec ++ ")"
cftySpec fc t = throw (GenericMsg fc ("Can't pass argument of type " ++ show t ++
                         " to foreign function"))

loadlib : String -> String -> String
loadlib "libc" _ = "(define-ffi-definer define-libc (ffi-lib #f))"
loadlib libn ver
    = "(define-ffi-definer define-" ++ libn ++
      " (ffi-lib \"" ++ libn ++ "\" " ++ ver ++ "))\n"

getLibVers : String -> (String, String)
getLibVers libspec
    = case words libspec of
           [] => ("", "")
           [fn] => case span (/='.') libspec of
                        (root, rest) => (root, "")
           (fn :: vers) =>
               (fst (span (/='.') fn),
                  "'(" ++ showSep " " (map show vers) ++ " #f)" )

cToRkt : CFType -> String -> String
cToRkt CFChar op = "(integer->char " ++ op ++ ")"
cToRkt _ op = op

rktToC : CFType -> String -> String
rktToC CFChar op = "(char->integer " ++ op ++ ")"
rktToC _ op = op

handleRet : CFType -> String -> String
handleRet CFUnit op = op ++ " " ++ mkWorld (schConstructor 0 [])
handleRet ret op = mkWorld (cToRkt ret op)

cCall : {auto f : Ref Done (List String) } ->
        {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        String -> FC -> (cfn : String) -> (clib : String) ->
        List (Name, CFType) -> CFType -> Core (String, String)
cCall appdir fc cfn clib args (CFIORes CFGCPtr)
    = throw (GenericMsg fc "Can't return GCPtr from a foreign function")
cCall appdir fc cfn clib args CFGCPtr
    = throw (GenericMsg fc "Can't return GCPtr from a foreign function")
cCall appdir fc cfn clib args (CFIORes CFBuffer)
    = throw (GenericMsg fc "Can't return Buffer from a foreign function")
cCall appdir fc cfn clib args CFBuffer
    = throw (GenericMsg fc "Can't return Buffer from a foreign function")
cCall appdir fc cfn libspec args ret
    = do loaded <- get Loaded
         bound <- get Done

         let (libn, vers) = getLibVers libspec
         lib <- if libn `elem` loaded
                   then pure ""
                   else do put Loaded (libn :: loaded)
                           (fname, fullname) <- locate libspec
                           copyLib (appdir </> fname, fullname)
                           pure (loadlib libn vers)

         argTypes <- traverse (\a => do s <- cftySpec fc (snd a)
                                        pure (a, s)) args
         retType <- cftySpec fc ret
         cbind <- if cfn `elem` bound
                     then pure ""
                     else do put Done (cfn :: bound)
                             pure $ "(define-" ++ libn ++ " " ++ cfn ++
                                    " (_fun " ++ showSep " " (map snd argTypes) ++ " -> " ++
                                        retType ++ "))\n"
         let call = "(" ++ cfn ++ " " ++
                    showSep " " !(traverse useArg (map fst argTypes)) ++ ")"

         pure (lib ++ cbind, case ret of
                                  CFIORes rt => handleRet rt call
                                  _ => call)
  where
    mkNs : Int -> List CFType -> List (Maybe (String, CFType))
    mkNs i [] = []
    mkNs i (CFWorld :: xs) = Nothing :: mkNs i xs
    mkNs i (x :: xs) = Just ("cb" ++ show i, x) :: mkNs (i + 1) xs

    applyLams : String -> List (Maybe (String, CFType)) -> String
    applyLams n [] = n
    applyLams n (Nothing :: as) = applyLams ("(" ++ n ++ " #f)") as
    applyLams n (Just (a, ty) :: as)
        = applyLams ("(" ++ n ++ " " ++ cToRkt ty a ++ ")") as

    mkFun : List CFType -> CFType -> String -> String
    mkFun args ret n
        = let argns = mkNs 0 args in
              "(lambda (" ++ showSep " " (map fst (mapMaybe id argns)) ++ ") " ++
              (applyLams n argns ++ ")")

    notWorld : CFType -> Bool
    notWorld CFWorld = False
    notWorld _ = True

    callback : String -> List CFType -> CFType -> Core String
    callback n args (CFFun s t) = callback n (s :: args) t
    callback n args_rev retty
        = do let args = reverse args_rev
             argTypes <- traverse (cftySpec fc) (filter notWorld args)
             retType <- cftySpec fc retty
             pure $ mkFun args retty n

    useArg : (Name, CFType) -> Core String
    useArg (n, CFFun s t) = callback (schName n) [s] t
    useArg (n, ty)
        = pure $ rktToC ty (schName n)

schemeCall : FC -> (sfn : String) ->
             List Name -> CFType -> Core String
schemeCall fc sfn argns ret
    = let call = "(" ++ sfn ++ " " ++ showSep " " (map schName argns) ++ ")" in
          case ret of
               CFIORes _ => pure $ mkWorld call
               _ => pure call

-- Use a calling convention to compile a foreign def.
-- Returns any preamble needed for loading libraries, and the body of the
-- function call.
useCC : {auto f : Ref Done (List String) } ->
        {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        String -> FC -> List String -> List (Name, CFType) -> CFType -> Core (String, String)
useCC appdir fc ccs args ret
    = case parseCC ["scheme,racket", "scheme", "C"] ccs of
           Nothing => throw (NoForeignCC fc ccs)
           Just ("scheme,racket", [sfn]) =>
               do body <- schemeCall fc sfn (map fst args) ret
                  pure ("", body)
           Just ("scheme", [sfn]) =>
               do body <- schemeCall fc sfn (map fst args) ret
                  pure ("", body)
           Just ("C", [cfn, clib]) => cCall appdir fc cfn clib args ret
           Just ("C", [cfn, clib, chdr]) => cCall appdir fc cfn clib args ret
           _ => throw (NoForeignCC fc ccs)

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
                    pure $ concat defs ++ "(define-cstruct _" ++ n ++ " ("
                           ++ showSep "\n\t" !(traverse showFld flds) ++ "))\n"
  where
    showFld : (String, CFType) -> Core String
    showFld (n, ty) = pure $ "[" ++ n ++ " " ++ !(cftySpec emptyFC ty) ++ "]"
mkStruct (CFIORes t) = mkStruct t
mkStruct (CFFun a b) = do ignore (mkStruct a); mkStruct b
mkStruct _ = pure ""

schFgnDef : {auto f : Ref Done (List String) } ->
            {auto c : Ref Ctxt Defs} ->
            {auto l : Ref Loaded (List String)} ->
            {auto s : Ref Structs (List String)} ->
            String -> FC -> Name -> NamedDef -> Core (String, String)
schFgnDef appdir fc n (MkNmForeign cs args ret)
    = do let argns = mkArgs 0 args
         let allargns = map fst argns
         let useargns = map fst (filter snd argns)
         argStrs <- traverse mkStruct args
         retStr <- mkStruct ret
         (load, body) <- useCC appdir fc cs (zip useargns args) ret
         defs <- get Ctxt
         pure (concat argStrs ++ retStr ++ load,
                "(define " ++ schName !(full (gamma defs) n) ++
                " (lambda (" ++ showSep " " (map schName allargns) ++ ") " ++
                body ++ "))\n")
schFgnDef _ _ _ _ = pure ("", "")

getFgnCall : {auto f : Ref Done (List String) } ->
             {auto c : Ref Ctxt Defs} ->
             {auto l : Ref Loaded (List String)} ->
             {auto s : Ref Structs (List String)} ->
             String -> (Name, FC, NamedDef) -> Core (String, String)
getFgnCall appdir (n, fc, d) = schFgnDef appdir fc n d

startRacket : String -> String -> String -> String
startRacket racket appdir target = unlines
    [ "#!/bin/sh"
    , "# " ++ (generatedString "Racket")
    , ""
    , "set -e # exit on any error"
    , ""
    , "if [ \"$(uname)\" = Darwin ]; then"
    , "  DIR=$(zsh -c 'printf %s \"$0:A:h\"' \"$0\")"
    , "else"
    , "  DIR=$(dirname \"$(readlink -f -- \"$0\")\")"
    , "fi"
    , ""
    , "export LD_LIBRARY_PATH=\"$DIR/" ++ appdir ++ "\":$LD_LIBRARY_PATH"
    , racket ++ "\"$DIR/" ++ target ++ "\" \"$@\""
    ]

startRacketCmd : String -> String -> String -> String
startRacketCmd racket appdir target = unlines
    [ "@echo off"
    , "set APPDIR=%~dp0"
    , "set PATH=%APPDIR%\\" ++ appdir ++ ";%PATH%"
    , racket ++ "\"" ++ target ++ "\" %*"
    ]

startRacketWinSh : String -> String -> String -> String
startRacketWinSh racket appdir target = unlines
    [ "#!/bin/sh"
    , "# " ++ (generatedString "Racket")
    , ""
    , "set -e # exit on any error"
    , ""
    , "DIR=$(dirname \"$(readlink -f -- \"$0\")\")"
    , "export PATH=\"$DIR/" ++ appdir ++ "\":$PATH"
    , racket ++ "\"" ++ target ++ "\" \"$@\""
    ]

compileToRKT : Ref Ctxt Defs ->
               String -> ClosedTerm -> (outfile : String) -> Core ()
compileToRKT c appdir tm outfile
    = do cdata <- getCompileData False Cases tm
         let ndefs = namedDefs cdata
         let ctm = forget (mainExpr cdata)

         defs <- get Ctxt
         f <- newRef {t = List String} Done empty
         l <- newRef {t = List String} Loaded []
         s <- newRef {t = List String} Structs []
         fgndefs <- traverse (getFgnCall appdir) ndefs
         compdefs <- traverse (getScheme racketPrim racketString) ndefs
         let code = fastAppend (map snd fgndefs ++ compdefs)
         main <- schExp racketPrim racketString 0 ctm
         support <- readDataFile "racket/support.rkt"
         ds <- getDirectives Racket
         extraRuntime <- getExtraRuntime ds
         let prof = profile !getSession
         let runmain
                = if prof
                     then "(profile (void " ++ main ++ ") #:order 'self)\n"
                     else "(void " ++ main ++ ")\n"
         let scm = schHeader prof (concat (map fst fgndefs)) ++
                   support ++ extraRuntime ++ code ++
                   runmain ++ schFooter
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift_ $ chmodRaw outfile 0o755
         pure ()

makeSh : String -> String -> String -> String -> Core ()
makeSh racket outShRel appdir outAbs
    = do Right () <- coreLift $ writeFile outShRel (startRacket racket appdir outAbs)
            | Left err => throw (FileErr outShRel err)
         pure ()

||| Make Windows start scripts, one for bash environments and one batch file
makeShWindows : String -> String -> String -> String -> Core ()
makeShWindows racket outShRel appdir outAbs
    = do let cmdFile = outShRel ++ ".cmd"
         Right () <- coreLift $ writeFile cmdFile (startRacketCmd racket appdir outAbs)
            | Left err => throw (FileErr cmdFile err)
         Right () <- coreLift $ writeFile outShRel (startRacketWinSh racket appdir outAbs)
            | Left err => throw (FileErr outShRel err)
         pure ()

compileExpr : Bool -> Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr mkexec c tmpDir outputDir tm outfile
    = do let appDirRel = outfile ++ "_app" -- relative to build dir
         let appDirGen = outputDir </> appDirRel -- relative to here
         coreLift_ $ mkdirAll appDirGen
         Just cwd <- coreLift currentDir
              | Nothing => throw (InternalError "Can't get current directory")

         let ext = if isWindows then ".exe" else ""
         let outRktFile = appDirRel </> outfile <.> "rkt"
         let outBinFile = appDirRel </> outfile <.> ext
         let outRktAbs = cwd </> outputDir </> outRktFile
         let outBinAbs = cwd </> outputDir </> outBinFile

         compileToRKT c appDirGen tm outRktAbs
         raco <- coreLift findRacoExe
         racket <- coreLift findRacket

         ok <- the (Core Int) $ if mkexec
                  then logTime "+ Build racket" $
                         coreLift $
                           system (raco ++ " -o " ++ outBinAbs ++ " " ++ outRktAbs)
                  else pure 0
         if ok == 0
            then do -- TODO: add launcher script
                    let outShRel = outputDir </> outfile
                    if isWindows
                       then if mkexec
                               then makeShWindows "" outShRel appDirRel outBinFile
                               else makeShWindows (racket ++ " ") outShRel appDirRel outRktFile
                       else if mkexec
                               then makeSh "" outShRel appDirRel outBinFile
                               else makeSh (racket ++ " ") outShRel appDirRel outRktFile
                    coreLift_ $ chmodRaw outShRel 0o755
                    pure (Just outShRel)
            else pure Nothing

executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm
    = do Just sh <- compileExpr False c tmpDir tmpDir tm "_tmpracket"
            | Nothing => throw (InternalError "compileExpr returned Nothing")
         coreLift_ $ system sh

export
codegenRacket : Codegen
codegenRacket = MkCG (compileExpr True) executeExpr Nothing Nothing
