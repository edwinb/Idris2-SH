module Idris.Env

--- All environment variables accessed by the compiler are enumerated in this module.

import public Data.List
import public Data.Maybe

import System

%default total

||| Environment variable used by Idris2 compiler
public export
record EnvDesc where
  constructor MkEnvDesc
  name : String
  help : String

||| All environment variables used by Idris2 compiler
public export
envs : List EnvDesc
envs = [
         MkEnvDesc "EDITOR"        "Editor used in REPL :e command",
         MkEnvDesc "IDRIS2_PREFIX" "Idris2 installation prefix",
         MkEnvDesc "IDRIS2_PATH"   "Places Idris2 looks for import files",
         MkEnvDesc "IDRIS2_PACKAGE_PATH" "Places Idris2 looks for packages",
         MkEnvDesc "IDRIS2_DATA"   "Places Idris2 looks for data files",
         MkEnvDesc "IDRIS2_LIBS"   "Places Idris2 looks for libraries (for code generation)",
         MkEnvDesc "IDRIS2_CG"     "Codegen backend",
         MkEnvDesc "IDRIS2_INC_CGS" "Code generators to use (comma separated) when compiling modules incrementally",
         MkEnvDesc "CHEZ"          "chez executable used in Chez codegen",
         MkEnvDesc "RACKET"        "racket executable used in Racket codegen",
         MkEnvDesc "RACKET_RACO"   "raco executable used in Racket codegen",
         MkEnvDesc "GAMBIT_GSI"    "gsi executable used in Gambit codegen",
         MkEnvDesc "GAMBIT_GSC"    "gsc executable used in Gambit codegen",
         MkEnvDesc "GAMBIT_GSC_BACKEND" "gsc executable backend argument",
         MkEnvDesc "IDRIS2_CC"     "C compiler executable used in RefC codegen",
         MkEnvDesc "CC"            "C compiler executable used in RefC codegen",
         MkEnvDesc "NODE"          "node executable used in Node codegen",
         MkEnvDesc "PATH"          "PATH variable is used to search for executables in certain codegens",
         MkEnvDesc "IDRIS_REFC_INTEGER" "Integer implementation used in RefC codegen, can be \"gmp\"(default) or \"libbf\""
       ]

--- `public export` only for `auto` to work in `idrisGetEnv`
public export
envNames : List String
envNames = map (.name) envs

||| Query documented environment variable
public export
idrisGetEnv : HasIO io => (name : String) ->
  {auto known : IsJust (find (name ==) Env.envNames)}
  -> io (Maybe String)
idrisGetEnv name = getEnv name
