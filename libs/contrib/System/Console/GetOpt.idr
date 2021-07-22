||| This library provides facilities for parsing the command-line options
||| in a standalone program. It is essentially an Idris port of the GNU getopt library.
||| (Actually, it is an Idris port of the [corresponding Haskell module]
||| (http://hackage.haskell.org/package/base-4.14.1.0/docs/System-Console-GetOpt.html)).
module System.Console.GetOpt

import Control.Monad.Reader
import Control.Monad.State

import Data.List
import Data.List1
import Data.Maybe
import Data.String

%default total

||| What to do with options following non-options
public export
data ArgOrder a =
  ||| no option processing after first non-option
  RequireOrder                |
  ||| freely intersperse options and non-options
  Permute                     |
  ||| wrap non-options into options
  ReturnInOrder (String -> a)

export
Functor ArgOrder where
  map _ RequireOrder      = RequireOrder
  map _ Permute           = Permute
  map f (ReturnInOrder g) = ReturnInOrder (f . g)

||| Describes whether an option takes an argument or not, and if so
||| how the argument is injected into a value of type `a`.
public export
data ArgDescr a =
   ||| no argument expected
   NoArg                   a         |
   ||| option requires argument
   ReqArg (String       -> a) String |
   ||| optional argument
   OptArg (Maybe String -> a) String

export
Functor ArgDescr where
  map f (NoArg x)    = NoArg (f x)
  map f (ReqArg g x) = ReqArg (f . g) x
  map f (OptArg g x) = OptArg (f . g) x

||| Each `OptDescr` describes a single option.
|||
||| The arguments to 'Option' are:
|||
||| * list of short option characters
||| * list of long option strings (without \"--\")
||| * argument descriptor
||| * explanation of option for user
public export
record OptDescr a where
  constructor MkOpt
  ||| list of short option characters
  shortNames  : List Char
  ||| list of long option strings (without "--")
  longNames   : List String
  ||| argument descriptor
  argDescr    : ArgDescr a
  ||| explanation of option for user
  description : String

export
Functor OptDescr where
  map f = record { argDescr $= map f }

-- kind of cmd line arg (internal use only):
data OptKind a
   = Opt       a                --    an option
   | UnreqOpt  String           --    an un-recognized option
   | NonOpt    String           --    a non-option
   | EndOfOpts                  --    end-of-options marker (i.e. "--")
   | OptErr    String           --    something went wrong...

--------------------------------------------------------------------------------
--          Printing Usage Info
--------------------------------------------------------------------------------

fmtShort : ArgDescr a -> Char -> String
fmtShort (NoArg  _   ) so = "-" ++ singleton so
fmtShort (ReqArg _ ad) so = "-" ++ singleton so ++ " " ++ ad
fmtShort (OptArg _ ad) so = "-" ++ singleton so ++ "[" ++ ad ++ "]"

fmtLong : ArgDescr a -> String -> String
fmtLong (NoArg  _   ) lo = "--" ++ lo
fmtLong (ReqArg _ ad) lo = "--" ++ lo ++ "=" ++ ad
fmtLong (OptArg _ ad) lo = "--" ++ lo ++ "[=" ++ ad ++ "]"

fmtOpt : OptDescr a -> List (String,String,String)
fmtOpt (MkOpt sos los ad descr) =
  let sosFmt = concat $ intersperse ", " (map (fmtShort ad) sos)
      losFmt = concat $ intersperse ", " (map (fmtLong ad) los)
      (h ::: t) = lines1 descr in
      (sosFmt,losFmt,h) :: map (\s => ("","",s)) t
  where lines1 : String -> List1 String
        lines1 s = case lines s of
                        [] => "" ::: []
                        (x :: xs) => x ::: xs

||| Return a string describing the usage of a command, derived from
||| the header (first argument) and the options described by the
||| second argument.
public export
usageInfo : (header : String) -> List (OptDescr a) -> String
usageInfo header optDescr =
  let (ss,ls,ds)   = (unzip3 . concatMap fmtOpt) optDescr
      paste        = \x,y,z => "  " ++ x ++ "  " ++ y ++ "  " ++ z
      table        = zipWith3 paste (sameLen ss) (sameLen ls) ds
   in unlines $ header :: table

  where flushLeft : Nat -> String -> String
        flushLeft n s = s ++ pack (replicate (n `minus` length s) ' ')

        sameLen : List String -> List String
        sameLen ss = let len = foldl (\n => max n . length) 0 ss
                      in map (flushLeft len) ss

--------------------------------------------------------------------------------
--          Error Formatting
--------------------------------------------------------------------------------

errAmbig : List (OptDescr a) -> (optStr : String) -> OptKind a
errAmbig ods s = let h = "option `" ++ s ++ "' is ambiguous; could be one of:"
                  in OptErr (usageInfo h ods)

errReq : String -> (optStr : String) -> OptKind a
errReq d s = OptErr ("option `" ++ s ++ "' requires an argument " ++ d ++ "\n")

errNoArg : (optStr : String) -> OptKind a
errNoArg s = OptErr ("option `" ++ s ++ "' doesn't allow an argument\n")

--------------------------------------------------------------------------------
--          Parsing Options
--------------------------------------------------------------------------------

||| Result of parsing the command line arguments accoring to a list
||| of `OptDescr`s. (see also function `getOpt`).
public export
record Result a where
  constructor MkResult
  ||| List of successfully parsed options
  options      : List a

  ||| List of non-options (other command line arguments)
  nonOptions   : List String

  ||| List of unrecognized options.
  unrecognized : List String

  ||| Errors during option parsing. These occur, for instance, when
  ||| an option requires an additional argument but none was given.
  errors       : List String

public export
emptyRes : Result a
emptyRes = MkResult [] [] [] []

export
Functor Result where
  map f = record { options $= map f }

OptFun : Type -> Type
OptFun a = List String -> List (OptDescr a) -> (OptKind a,List String)

longOpt : String -> OptFun a
longOpt ls rs descs =
  let (opt,arg) = break ('=' ==) ls
      getWith   = \p => filter (any (p opt) . longNames) descs
      exact     = getWith (==)
      options   = if null exact then getWith isPrefixOf else exact
      ads       = map argDescr options
      os        = "--" ++ opt
   in case (ads,unpack arg,rs) of
           (_ :: _ :: _ , _      ,  r        ) => (errAmbig options os, r)
           ([NoArg  a  ], []     ,  r        ) => (Opt a, r)
           ([NoArg  a  ], c :: _ ,  r        ) => (errNoArg os,r)
--                        ^ this is known (but not proven) to be '='

           ([ReqArg _ d], []     ,  []       ) => (errReq d os,[])
           ([ReqArg f _], []     ,  (r::rest)) => (Opt $ f r,rest)
           ([ReqArg f _], c :: xs,  r        ) => (Opt $ f (pack xs),r)
--                        ^ this is known (but not proven) to be '='

           ([OptArg f _], []     ,  r        ) => (Opt $ f Nothing,r)
           ([OptArg f _], c :: xs,  r        ) => (Opt . f . Just $ pack xs,r)
--                        ^ this is known (but not proven) to be '='

           ([]          , _      ,  r        ) => (UnreqOpt $ "--" ++ ls,r)

shortOpt : Char -> String -> OptFun a
shortOpt y ys rs descs =
  let options = filter (elem y . shortNames) descs
      ads     = map argDescr options
      mkOs    = strCons '-'
      os      = mkOs (singleton y)
   in case (ads,ys,rs) of
           (_ :: _ :: _ , _ ,  r        ) => (errAmbig options os, r)
           ([NoArg  a  ], "",  r        ) => (Opt a,r)
           ([NoArg  a  ], s ,  r        ) => (Opt a, mkOs s :: r)
           ([ReqArg _ d], "",  []       ) => (errReq d os, [])
           ([ReqArg f _], "",  (r::rest)) => (Opt $ f r, rest)
           ([ReqArg f _], s ,  r        ) => (Opt $ f s, r)
           ([OptArg f _], "",  r        ) => (Opt $ f Nothing, r)
           ([OptArg f _], s ,  r        ) => (Opt . f $ Just s, r)
           ([]          , "",  r        ) => (UnreqOpt os, r)
           ([]          , s ,  r        ) => (UnreqOpt os, mkOs s :: r)


-- take a look at the next cmd line arg and decide what to do with it
getNext : List Char -> OptFun a
getNext ('-'::'-'::[]) r _        = (EndOfOpts,r)
getNext ('-'::'-'::xs) r descs    = longOpt (pack xs) r descs
getNext ('-':: x ::xs) r descs    = shortOpt x (pack xs) r descs
getNext a              r _        = (NonOpt $ pack a,r)

||| Process the command-line, and return the list of values that matched
||| (and those that didn't). The arguments are:
|||
||| * The order requirements (see `ArgOrder`)
|||
||| * The option descriptions (see `OptDescr`)
|||
||| * The actual command line arguments (presumably got from
|||   `System.getArgs`).
export
getOpt :  ArgOrder a                         -- non-option handling
       -> List (OptDescr a)                  -- option descriptors
       -> (args : List String)               -- the command-line arguments
       -> Result a
getOpt _        _        []         =  emptyRes
getOpt ordering descs (arg::args)   =
  let (opt,rest) = getNext (unpack arg) args descs
      res        = getOpt ordering descs rest
   in case (opt,ordering) of
           (Opt x, _)                   => {options $= (x::)} res
           (UnreqOpt x, _)              => {unrecognized $= (x::)} res
           (NonOpt x, RequireOrder)     => MkResult [] (x::rest) [] []
           (NonOpt x, Permute)          => {nonOptions $= (x::)} res
           (NonOpt x, ReturnInOrder f)  => {options $= (f x::)} res
           (EndOfOpts, RequireOrder)    => MkResult [] rest [] []
           (EndOfOpts, Permute)         => MkResult [] rest [] []
           (EndOfOpts, ReturnInOrder f) => MkResult (map f rest) [] [] []
           (OptErr e, _)                => {errors $= (e::)} res
