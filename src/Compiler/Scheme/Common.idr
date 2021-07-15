module Compiler.Scheme.Common

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.Vect

import System.Info

%default covering

export
firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

schString : String -> String
schString s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c || c =='_'
                  then cast c
                  else "C-" ++ show (cast {to=Int} c)

export
schName : Name -> String
schName (NS ns (UN n)) = schString (showNSWithSep "-" ns) ++ "-" ++ schString n
schName (NS ns n) = schString (showNSWithSep "-" ns) ++ "-" ++ schName n
schName (UN n) = "u--" ++ schString n
schName (MN n i) = schString n ++ "-" ++ show i
schName (PV n d) = "pat--" ++ schName n
schName (DN _ n) = schName n
schName (RF n) = "rf--" ++ schString n
schName (Nested (i, x) n) = "n--" ++ show i ++ "-" ++ show x ++ "-" ++ schName n
schName (CaseBlock x y) = "case--" ++ schString x ++ "-" ++ show y
schName (WithBlock x y) = "with--" ++ schString x ++ "-" ++ show y
schName (Resolved i) = "fn--" ++ show i

export
schConstructor : Int -> List String -> String
schConstructor t args
    = "(vector " ++ show t ++ " " ++ showSep " " args ++ ")"

export
schRecordCon : List String -> String
schRecordCon args = "(vector " ++ showSep " " args ++ ")"

||| Generate scheme for a plain function.
op : String -> List String -> String
op o args = "(" ++ o ++ " " ++ showSep " " args ++ ")"

||| Generate scheme for a boolean operation.
boolop : String -> List String -> String
boolop o args = "(or (and " ++ op o args ++ " 1) 0)"

add : Maybe IntKind -> String -> String -> String
add (Just $ Signed $ P n)   x y = op "bs+" [x, y, show (n-1)]
add (Just $ Unsigned n)     x y = op "bu+" [x, y, show n]
add _                       x y = op "+" [x, y]

sub : Maybe IntKind -> String -> String -> String
sub (Just $ Signed $ P n)   x y = op "bs-" [x, y, show (n-1)]
sub (Just $ Unsigned n)     x y = op "bu-" [x, y, show n]
sub _                       x y = op "-" [x, y]

mul : Maybe IntKind -> String -> String -> String
mul (Just $ Signed $ P n)   x y = op "bs*" [x, y, show (n-1)]
mul (Just $ Unsigned n)     x y = op "bu*" [x, y, show n]
mul _                       x y = op "*" [x, y]

div : Maybe IntKind -> String -> String -> String
div (Just $ Signed Unlimited) x y = op "quotient" [x, y]
div (Just $ Signed $ P n)     x y = op "bs/" [x, y, show (n-1)]
div (Just $ Unsigned n)       x y = op "bu/" [x, y, show n]
div _                         x y = op "/" [x, y]

shl : Maybe IntKind -> String -> String -> String
shl (Just $ Signed $ P n) x y = op "blodwen-bits-shl-signed"
                                   [x, y, show (n-1)]
shl (Just $ Unsigned n)   x y = op "blodwen-bits-shl" [x, y, show n]
shl _                     x y = op "blodwen-shl" [x, y]


constPrimitives : ConstantPrimitives
constPrimitives = MkConstantPrimitives {
    charToInt    = \k     => pure . charTo k
  , intToChar    = \_,x   => pure $ op "cast-int-char" [x]
  , stringToInt  = \k     => pure . strTo k
  , intToString  = \_,x   => pure $ op "number->string" [x]
  , doubleToInt  = \k     => pure . dblTo k
  , intToDouble  = \_,x   => pure $ op "exact->inexact" [x]
  , intToInt     = \k1,k2 => pure . intTo k1 k2
  }
  where charTo : IntKind -> String -> String
        charTo (Signed Unlimited) x = op "char->integer" [x]
        charTo (Signed $ P n)     x = op "cast-char-boundedInt" [x, show (n-1)]
        charTo (Unsigned n)       x = op "cast-char-boundedUInt" [x,show n]

        strTo : IntKind -> String -> String
        strTo (Signed Unlimited) x = op "cast-string-int" [x]
        strTo (Signed $ P n)     x = op "cast-string-boundedInt" [x, show (n-1)]
        strTo (Unsigned n)       x = op "cast-string-boundedUInt" [x,show n]

        dblTo : IntKind -> String -> String
        dblTo (Signed Unlimited) x = op "exact-truncate" [x]
        dblTo (Signed $ P n)     x = op "exact-truncate-boundedInt" [x, show (n-1)]
        dblTo (Unsigned n)       x = op "exact-truncate-boundedUInt" [x,show n]

        intTo : IntKind -> IntKind -> String -> String
        intTo _ (Signed Unlimited) x = x
        intTo (Signed m) (Signed $ P n) x =
          if P n >= m then x else op "blodwen-toSignedInt" [x,show (n-1)]

        -- Only if the precision of the target is greater
        -- than the one of the source, there is no need to cast.
        intTo (Unsigned m) (Signed $ P n) x =
          if n > m then x else op "blodwen-toSignedInt" [x,show (n-1)]

        intTo (Signed _) (Unsigned n) x = op "blodwen-toUnsignedInt" [x,show n]

        intTo (Unsigned m) (Unsigned n) x =
          if n >= m then x else op "blodwen-toUnsignedInt" [x,show n]

||| Generate scheme for a primitive function.
schOp : {0 arity : Nat} -> PrimFn arity -> Vect arity String -> Core String
schOp (Add ty) [x, y] = pure $ add (intKind ty) x y
schOp (Sub ty) [x, y] = pure $ sub (intKind ty) x y
schOp (Mul ty) [x, y] = pure $ mul (intKind ty) x y
schOp (Div ty) [x, y] = pure $ div (intKind ty) x y
schOp (Mod ty) [x, y] = pure $ op "remainder" [x, y]
schOp (Neg ty) [x] = pure $ op "-" [x]
schOp (ShiftL ty) [x, y] = pure $ shl (intKind ty) x y
schOp (ShiftR ty) [x, y] = pure $ op "blodwen-shr" [x, y]
schOp (BAnd ty) [x, y] = pure $ op "blodwen-and" [x, y]
schOp (BOr ty) [x, y] = pure $ op "blodwen-or" [x, y]
schOp (BXOr ty) [x, y] = pure $ op "blodwen-xor" [x, y]
schOp (LT CharType) [x, y] = pure $ boolop "char<?" [x, y]
schOp (LTE CharType) [x, y] = pure $ boolop "char<=?" [x, y]
schOp (EQ CharType) [x, y] = pure $ boolop "char=?" [x, y]
schOp (GTE CharType) [x, y] = pure $ boolop "char>=?" [x, y]
schOp (GT CharType) [x, y] = pure $ boolop "char>?" [x, y]
schOp (LT StringType) [x, y] = pure $ boolop "string<?" [x, y]
schOp (LTE StringType) [x, y] = pure $ boolop "string<=?" [x, y]
schOp (EQ StringType) [x, y] = pure $ boolop "string=?" [x, y]
schOp (GTE StringType) [x, y] = pure $ boolop "string>=?" [x, y]
schOp (GT StringType) [x, y] = pure $ boolop "string>?" [x, y]
schOp (LT ty) [x, y] = pure $ boolop "<" [x, y]
schOp (LTE ty) [x, y] = pure $ boolop "<=" [x, y]
schOp (EQ ty) [x, y] = pure $ boolop "=" [x, y]
schOp (GTE ty) [x, y] = pure $ boolop ">=" [x, y]
schOp (GT ty) [x, y] = pure $ boolop ">" [x, y]
schOp StrLength [x] = pure $ op "string-length" [x]
schOp StrHead [x] = pure $ op "string-ref" [x, "0"]
schOp StrTail [x] = pure $ op "substring" [x, "1", op "string-length" [x]]
schOp StrIndex [x, i] = pure $ op "string-ref" [x, i]
schOp StrCons [x, y] = pure $ op "string-cons" [x, y]
schOp StrAppend [x, y] = pure $ op "string-append" [x, y]
schOp StrReverse [x] = pure $ op "string-reverse" [x]
schOp StrSubstr [x, y, z] = pure $ op "string-substr" [x, y, z]

-- `e` is Euler's number, which approximates to: 2.718281828459045
schOp DoubleExp [x] = pure $ op "flexp" [x] -- Base is `e`. Same as: `pow(e, x)`
schOp DoubleLog [x] = pure $ op "fllog" [x] -- Base is `e`.
schOp DoubleSin [x] = pure $ op "flsin" [x]
schOp DoubleCos [x] = pure $ op "flcos" [x]
schOp DoubleTan [x] = pure $ op "fltan" [x]
schOp DoubleASin [x] = pure $ op "flasin" [x]
schOp DoubleACos [x] = pure $ op "flacos" [x]
schOp DoubleATan [x] = pure $ op "flatan" [x]
schOp DoubleSqrt [x] = pure $ op "flsqrt" [x]
schOp DoubleFloor [x] = pure $ op "flfloor" [x]
schOp DoubleCeiling [x] = pure $ op "flceiling" [x]

schOp (Cast DoubleType StringType)  [x] = pure $ op "number->string" [x]
schOp (Cast CharType StringType)    [x] = pure $ op "string" [x]
schOp (Cast StringType DoubleType)  [x] = pure $ op "cast-string-double" [x]

schOp (Cast from to)                [x] = castInt constPrimitives from to x

schOp BelieveMe [_,_,x] = pure x
schOp Crash [_,msg] = pure $ "(blodwen-error-quit (string-append \"ERROR: \" " ++ msg ++ "))"

||| Extended primitives for the scheme backend, outside the standard set of primFn
public export
data ExtPrim = NewIORef | ReadIORef | WriteIORef
             | NewArray | ArrayGet | ArraySet
             | GetField | SetField
             | VoidElim
             | SysOS | SysCodegen
             | OnCollect
             | OnCollectAny
             | MakeFuture
             | Unknown Name

export
Show ExtPrim where
  show NewIORef = "NewIORef"
  show ReadIORef = "ReadIORef"
  show WriteIORef = "WriteIORef"
  show NewArray = "NewArray"
  show ArrayGet = "ArrayGet"
  show ArraySet = "ArraySet"
  show GetField = "GetField"
  show SetField = "SetField"
  show VoidElim = "VoidElim"
  show SysOS = "SysOS"
  show SysCodegen = "SysCodegen"
  show OnCollect = "OnCollect"
  show OnCollectAny = "OnCollectAny"
  show MakeFuture = "MakeFuture"
  show (Unknown n) = "Unknown " ++ show n

||| Match on a user given name to get the scheme primitive
toPrim : Name -> ExtPrim
toPrim pn@(NS _ n)
    = cond [(n == UN "prim__newIORef", NewIORef),
            (n == UN "prim__readIORef", ReadIORef),
            (n == UN "prim__writeIORef", WriteIORef),
            (n == UN "prim__newArray", NewArray),
            (n == UN "prim__arrayGet", ArrayGet),
            (n == UN "prim__arraySet", ArraySet),
            (n == UN "prim__getField", GetField),
            (n == UN "prim__setField", SetField),
            (n == UN "void", VoidElim), -- DEPRECATED. TODO: remove when bootstrap has been updated
            (n == UN "prim__void", VoidElim),
            (n == UN "prim__os", SysOS),
            (n == UN "prim__codegen", SysCodegen),
            (n == UN "prim__onCollect", OnCollect),
            (n == UN "prim__onCollectAny", OnCollectAny),
            (n == UN "prim__makeFuture", MakeFuture)
            ]
           (Unknown pn)
toPrim pn = Unknown pn

export
mkWorld : String -> String
mkWorld res = res -- MkIORes is a newtype now! schConstructor 0 [res, "#f"] -- MkIORes

schConstant : (String -> String) -> Constant -> String
schConstant _ (I x) = show x
schConstant _ (I8 x) = show x
schConstant _ (I16 x) = show x
schConstant _ (I32 x) = show x
schConstant _ (I64 x) = show x
schConstant _ (BI x) = show x
schConstant _ (B8 x) = show x
schConstant _ (B16 x) = show x
schConstant _ (B32 x) = show x
schConstant _ (B64 x) = show x
schConstant schString (Str x) = schString x
schConstant _ (Ch x)
   = if (the Int (cast x) >= 32 && the Int (cast x) < 127)
        then "#\\" ++ cast x
        else "(integer->char " ++ show (the Int (cast x)) ++ ")"
schConstant _ (Db x) = show x
schConstant _ WorldVal = "#f"
schConstant _ IntType = "#t"
schConstant _ Int8Type = "#t"
schConstant _ Int16Type = "#t"
schConstant _ Int32Type = "#t"
schConstant _ Int64Type = "#t"
schConstant _ IntegerType = "#t"
schConstant _ Bits8Type = "#t"
schConstant _ Bits16Type = "#t"
schConstant _ Bits32Type = "#t"
schConstant _ Bits64Type = "#t"
schConstant _ StringType = "#t"
schConstant _ CharType = "#t"
schConstant _ DoubleType = "#t"
schConstant _ WorldType = "#t"

schCaseDef : Maybe String -> String
schCaseDef Nothing = ""
schCaseDef (Just tm) = "(else " ++ tm ++ ")"

export
schArglist : List Name -> String
schArglist [] = ""
schArglist [x] = schName x
schArglist (x :: xs) = schName x ++ " " ++ schArglist xs

mutual
  used : Name -> NamedCExp -> Bool
  used n (NmLocal fc n') = n == n'
  used n (NmRef _ _) = False
  used n (NmLam _ _ sc) = used n sc
  used n (NmLet _ _ v sc) = used n v || used n sc
  used n (NmApp _ f args) = used n f || any (used n) args
  used n (NmCon _ _ _ _ args) = any (used n) args
  used n (NmOp _ _ args) = any (used n) (toList args)
  used n (NmExtPrim _ _ args) = any (used n) args
  used n (NmForce _ _ t) = used n t
  used n (NmDelay _ _ t) = used n t
  used n (NmConCase _ sc alts def)
      = used n sc || any (usedCon n) alts
            || maybe False (used n) def
  used n (NmConstCase _ sc alts def)
      = used n sc || any (usedConst n) alts
            || maybe False (used n) def
  used n _ = False

  usedCon : Name -> NamedConAlt -> Bool
  usedCon n (MkNConAlt _ _ _ _ sc) = used n sc

  usedConst : Name -> NamedConstAlt -> Bool
  usedConst n (MkNConstAlt _ sc) = used n sc

var : NamedCExp -> Bool
var (NmLocal _ _) = True
var _ = False

parameters (schExtPrim : Int -> ExtPrim -> List NamedCExp -> Core String,
            schString : String -> String)

  mutual
    schConAlt : Int -> String -> NamedConAlt -> Core String
    schConAlt i target (MkNConAlt n ci tag args sc)
        = pure $ "((" ++ show tag ++ ") "
                      ++ bindArgs 1 args !(schExp i sc) ++ ")"
      where
        bindArgs : Int -> (ns : List Name) -> String -> String
        bindArgs i [] body = body
        bindArgs i (n :: ns) body
            = if used n sc
                 then "(let ((" ++ schName n ++ " " ++ "(vector-ref " ++ target ++ " " ++ show i ++ "))) "
                    ++ bindArgs (i + 1) ns body ++ ")"
                 else bindArgs (i + 1) ns body

    schConUncheckedAlt : Int -> String -> NamedConAlt -> Core String
    schConUncheckedAlt i target (MkNConAlt n ci tag args sc)
        = pure $ bindArgs 1 args !(schExp i sc)
      where
        bindArgs : Int -> (ns : List Name) -> String -> String
        bindArgs i [] body = body
        bindArgs i (n :: ns) body
            = if used n sc
                 then "(let ((" ++ schName n ++ " " ++ "(vector-ref " ++ target ++ " " ++ show i ++ "))) "
                    ++ bindArgs (i + 1) ns body ++ ")"
                 else bindArgs (i + 1) ns body

    schConstAlt : Int -> String -> NamedConstAlt -> Core String
    schConstAlt i target (MkNConstAlt c exp)
        = pure $ "((equal? " ++ target ++ " " ++ schConstant schString c ++ ") " ++ !(schExp i exp) ++ ")"

    -- oops, no traverse for Vect in Core
    schArgs : Int -> Vect n NamedCExp -> Core (Vect n String)
    schArgs i [] = pure []
    schArgs i (arg :: args) = pure $ !(schExp i arg) :: !(schArgs i args)

    schCaseTree : Int -> NamedCExp -> List NamedConAlt -> Maybe NamedCExp ->
                  Core String
    schCaseTree i sc [] def
        = do tcode <- schExp (i+1) sc
             defc <- maybe (pure "'erased") (schExp i) def
             let n = "sc" ++ show i
             if var sc
                then pure defc
                else pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) "
                             ++ defc ++ ")"
    schCaseTree i sc [alt] Nothing
        = do tcode <- schExp (i+1) sc
             let n = "sc" ++ show i
             if var sc
                then pure !(schConUncheckedAlt (i+1) tcode alt)
                else pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) " ++
                        !(schConUncheckedAlt (i+1) n alt) ++ ")"
    schCaseTree i sc alts Nothing
        = do tcode <- schExp (i+1) sc
             let n = "sc" ++ show i
             if var sc
                then pure $ "(case (vector-ref " ++ tcode ++ " 0) "
                       ++ !(showAlts tcode alts) ++
                       ")"
                else pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (case (vector-ref " ++ n ++ " 0) "
                       ++ !(showAlts n alts) ++
                       "))"
      where
        showAlts : String -> List NamedConAlt -> Core String
        showAlts n [] = pure ""
        showAlts n [alt]
           = pure $ "(else " ++ !(schConUncheckedAlt (i + 1) n alt) ++ ")"
        showAlts n (alt :: alts)
           = pure $ !(schConAlt (i + 1) n alt) ++ " " ++
                    !(showAlts n alts)
    schCaseTree i sc alts def
        = do tcode <- schExp (i+1) sc
             defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i v))) def
             let n = "sc" ++ show i
             if var sc
                then pure $ "(case (vector-ref " ++ tcode ++ " 0) "
                               ++ showSep " " !(traverse (schConAlt (i+1) tcode) alts)
                               ++ schCaseDef defc ++ ")"
                else pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (case (vector-ref " ++ n ++ " 0) "
                       ++ showSep " " !(traverse (schConAlt (i+1) n) alts)
                       ++ schCaseDef defc ++ "))"

    schRecordCase : Int -> NamedCExp -> List NamedConAlt -> Maybe NamedCExp ->
                    Core String
    schRecordCase i sc [] _ = pure "#f" -- suggests empty case block!
    schRecordCase i sc (alt :: _) _
        = do tcode <- schExp (i+1) sc
             let n = "sc" ++ show i
             if var sc
                then getAltCode tcode alt
                else do alt' <- getAltCode n alt
                        pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) " ++
                                     alt' ++ ")"
      where
        bindArgs : Int -> String -> (ns : List Name) -> String ->
                   NamedCExp -> String
        bindArgs i target [] body sc = body
        bindArgs i target (n :: ns) body sc
            = if used n sc
                 then "(let ((" ++ schName n ++ " " ++ "(vector-ref " ++ target ++ " " ++ show i ++ "))) "
                    ++ bindArgs (i + 1) target ns body sc ++ ")"
                 else bindArgs (i + 1) target ns body sc

        getAltCode : String -> NamedConAlt -> Core String
        getAltCode n (MkNConAlt _ _ _ args sc)
            = pure $ bindArgs 0 n args !(schExp i sc) sc

    schListCase : Int -> NamedCExp -> List NamedConAlt -> Maybe NamedCExp ->
                  Core String
    schListCase i sc alts def
        = do tcode <- schExp (i+1) sc
             let n = "sc" ++ show i
             defc <- maybe (pure Nothing)
                           (\v => pure (Just !(schExp (i + 1) v))) def
             nil <- getNilCode alts
             if var sc
                then do cons <- getConsCode tcode alts
                        pure $ buildCase tcode nil cons defc
                else do cons <- getConsCode n alts
                        pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) " ++
                            buildCase n nil cons defc ++ ")"
      where
        buildCase : String ->
                    Maybe String -> Maybe String -> Maybe String ->
                    String
        buildCase n (Just nil) (Just cons) _
            = "(if (null? " ++ n ++ ") " ++ nil ++ " " ++ cons ++ ")"
        buildCase n (Just nil) Nothing Nothing = nil
        buildCase n Nothing (Just cons) Nothing = cons
        buildCase n (Just nil) Nothing (Just def)
            = "(if (null? " ++ n ++ ") " ++ nil ++ " " ++ def ++ ")"
        buildCase n Nothing (Just cons) (Just def)
            = "(if (null? " ++ n ++ ") " ++ def ++ " " ++ cons ++ ")"
        buildCase n Nothing Nothing (Just def) = def
        buildCase n Nothing Nothing Nothing = "#f"

        getNilCode : List NamedConAlt -> Core (Maybe String)
        getNilCode [] = pure Nothing
        getNilCode (MkNConAlt _ NIL _ _ sc :: _)
            = pure (Just !(schExp (i + 1) sc))
        getNilCode (_ :: xs) = getNilCode xs

        getConsCode : String -> List NamedConAlt -> Core (Maybe String)
        getConsCode n [] = pure Nothing
        getConsCode n (MkNConAlt _ CONS _ [x,xs] sc :: _)
            = do sc' <- schExp (i + 1) sc
                 pure $ Just $ bindArgs [(x, "car"), (xs, "cdr")] sc'
          where
            bindArgs : (ns : List (Name, String)) -> String -> String
            bindArgs [] body = body
            bindArgs ((x, get) :: ns) body
                = if used x sc
                     then "(let ((" ++ schName x ++ " " ++ "(" ++ get ++ " " ++ n ++ "))) "
                        ++ bindArgs ns body ++ ")"
                     else bindArgs ns body
        getConsCode x (_ :: xs) = getConsCode x xs

    schMaybeCase : Int -> NamedCExp -> List NamedConAlt -> Maybe NamedCExp ->
                   Core String
    schMaybeCase i sc alts def
        = do tcode <- schExp (i+1) sc
             let n = "sc" ++ show i
             defc <- maybe (pure Nothing)
                           (\v => pure (Just !(schExp (i + 1) v))) def
             nothing <- getNothingCode alts
             if var sc
                then do just <- getJustCode tcode alts
                        pure $ buildCase tcode nothing just defc
                else do just <- getJustCode n alts
                        pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) " ++
                            buildCase n nothing just defc ++ ")"
      where
        buildCase : String ->
                    Maybe String -> Maybe String -> Maybe String ->
                    String
        buildCase n (Just nothing) (Just just) _
            = "(if (null? " ++ n ++ ") " ++ nothing ++ " " ++ just ++ ")"
        buildCase n (Just nothing) Nothing Nothing = nothing
        buildCase n Nothing (Just just) Nothing = just
        buildCase n (Just nothing) Nothing (Just def)
            = "(if (null? " ++ n ++ ") " ++ nothing ++ " " ++ def ++ ")"
        buildCase n Nothing (Just just) (Just def)
            = "(if (null? " ++ n ++ ") " ++ def ++ " " ++ just ++ ")"
        buildCase n Nothing Nothing (Just def) = def
        buildCase n Nothing Nothing Nothing = "#f"

        getNothingCode : List NamedConAlt -> Core (Maybe String)
        getNothingCode [] = pure Nothing
        getNothingCode (MkNConAlt _ NOTHING _ _ sc :: _)
            = pure (Just !(schExp (i + 1) sc))
        getNothingCode (_ :: xs) = getNothingCode xs

        getJustCode : String -> List NamedConAlt -> Core (Maybe String)
        getJustCode n [] = pure Nothing
        getJustCode n (MkNConAlt _ JUST _ [x] sc :: _)
            = do sc' <- schExp (i + 1) sc
                 pure $ Just $ bindArg x sc'
          where
            bindArg : Name -> String -> String
            bindArg x body
                = if used x sc
                     then "(let ((" ++ schName x ++ " " ++ "(unbox " ++ n ++ "))) "
                        ++ body ++ ")"
                     else body
        getJustCode x (_ :: xs) = getJustCode x xs

    export
    schExp : Int -> NamedCExp -> Core String
    schExp i (NmLocal fc n) = pure $ schName n
    schExp i (NmRef fc n) = pure $ schName n
    schExp i (NmLam fc x sc)
       = do sc' <- schExp i  sc
            pure $ "(lambda (" ++ schName x ++ ") " ++ sc' ++ ")"
    schExp i (NmLet fc x val sc)
       = do val' <- schExp i val
            sc' <- schExp i sc
            pure $ "(let ((" ++ schName x ++ " " ++ val' ++ ")) " ++ sc' ++ ")"
    schExp i (NmApp fc x [])
        = pure $ "(" ++ !(schExp i x) ++ ")"
    schExp i (NmApp fc x args)
        = pure $ "(" ++ !(schExp i x) ++ " " ++ showSep " " !(traverse (schExp i) args) ++ ")"
    schExp i (NmCon fc _ NIL tag []) = pure $ "'()"
    schExp i (NmCon fc _ NIL tag _) = throw (InternalError "Bad NIL")
    schExp i (NmCon fc _ CONS tag [x, xs])
        = do x' <- schExp i x
             xs' <- schExp i xs
             pure $ "(cons " ++ x' ++ " " ++ xs' ++ ")"
    schExp i (NmCon fc _ CONS tag _) = throw (InternalError "Bad CONS")
    schExp i (NmCon fc _ NOTHING tag []) = pure $ "'()"
    schExp i (NmCon fc _ NOTHING tag _) = throw (InternalError "Bad NOTHING")
    schExp i (NmCon fc _ JUST tag [x])
        = do x' <- schExp i x
             pure $ "(box " ++ x' ++ ")"
    schExp i (NmCon fc _ JUST tag _) = throw (InternalError "Bad JUST")
    schExp i (NmCon fc x RECORD tag args)
        = pure $ schRecordCon !(traverse (schExp i) args)
    schExp i (NmCon fc x ci tag args)
        = pure $ schConstructor tag !(traverse (schExp i) args)
    schExp i (NmOp fc op args)
        = schOp op !(schArgs i args)
    schExp i (NmExtPrim fc p args)
        = schExtPrim i (toPrim p) args
    schExp i (NmForce fc lr t) = pure $ "(" ++ !(schExp i t) ++ ")"
    schExp i (NmDelay fc lr t) = pure $ "(lambda () " ++ !(schExp i t) ++ ")"
    schExp i (NmConCase fc sc alts def)
        = cond [(recordCase alts, schRecordCase i sc alts def),
                (maybeCase alts, schMaybeCase i sc alts def),
                (listCase alts, schListCase i sc alts def)]
                -- probably more to come here...
                (schCaseTree i sc alts def)
      where
        listCase : List NamedConAlt -> Bool
        listCase (MkNConAlt _ NIL _ _ _ :: _) = True
        listCase (MkNConAlt _ CONS _ _ _ :: _) = True
        listCase _ = False

        maybeCase : List NamedConAlt -> Bool
        maybeCase (MkNConAlt _ NOTHING _ _ _ :: _) = True
        maybeCase (MkNConAlt _ JUST _ _ _ :: _) = True
        maybeCase _ = False

        recordCase : List NamedConAlt -> Bool
        recordCase (MkNConAlt _ RECORD _ _ _ :: _) = True
        recordCase _ = False

    schExp i (NmConstCase fc sc alts Nothing)
        = do tcode <- schExp (i+1) sc
             let n = "sc" ++ show i
             if var sc
                then pure $ "(cond "
                          ++ !(showConstAlts tcode alts)
                          ++ ")"
                else pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (cond "
                          ++ !(showConstAlts n alts)
                          ++ "))"
      where
        showConstAlts : String -> List NamedConstAlt -> Core String
        showConstAlts n [] = pure ""
        showConstAlts n [MkNConstAlt c exp]
           = pure $ "(else " ++ !(schExp (i + 1) exp) ++ ")"
        showConstAlts n (alt :: alts)
           = pure $ !(schConstAlt (i + 1) n alt) ++ " " ++
                    !(showConstAlts n alts)
    schExp i (NmConstCase fc sc alts def)
        = do defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i v))) def
             tcode <- schExp (i+1) sc
             let n = "sc" ++ show i
             if var sc
                then pure $ "(cond "
                          ++ showSep " " !(traverse (schConstAlt (i+1) tcode) alts)
                          ++ schCaseDef defc ++ ")"
                else pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (cond "
                          ++ showSep " " !(traverse (schConstAlt (i+1) n) alts)
                          ++ schCaseDef defc ++ "))"
    schExp i (NmPrimVal fc c) = pure $ schConstant schString c
    schExp i (NmErased fc) = pure "'erased"
    schExp i (NmCrash fc msg) = pure $ "(blodwen-error-quit " ++ show msg ++ ")"

  fileOp : String -> String
  fileOp op = "(blodwen-file-op (lambda () " ++ op ++ "))"

  -- External primitives which are common to the scheme codegens (they can be
  -- overridden)
  export
  schExtCommon : Int -> ExtPrim -> List NamedCExp -> Core String
  schExtCommon i NewIORef [_, val, world]
      = pure $ mkWorld $ "(box " ++ !(schExp i val) ++ ")"
  schExtCommon i ReadIORef [_, ref, world]
      = pure $ mkWorld $ "(unbox " ++ !(schExp i ref) ++ ")"
  schExtCommon i WriteIORef [_, ref, val, world]
      = pure $ mkWorld $ "(set-box! "
                           ++ !(schExp i ref) ++ " "
                           ++ !(schExp i val) ++ ")"
  schExtCommon i NewArray [_, size, val, world]
      = pure $ mkWorld $ "(make-vector " ++ !(schExp i size) ++ " "
                                         ++ !(schExp i val) ++ ")"
  schExtCommon i ArrayGet [_, arr, pos, world]
      = pure $ mkWorld $ "(vector-ref " ++ !(schExp i arr) ++ " "
                                        ++ !(schExp i pos) ++ ")"
  schExtCommon i ArraySet [_, arr, pos, val, world]
      = pure $ mkWorld $ "(vector-set! " ++ !(schExp i arr) ++ " "
                                         ++ !(schExp i pos) ++ " "
                                         ++ !(schExp i val) ++ ")"
  schExtCommon i VoidElim [_, _]
      = pure "(display \"Error: Executed 'void'\")"
  schExtCommon i SysOS []
      = pure $ "(blodwen-os)"
  schExtCommon i (Unknown n) args
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  schExtCommon i prim args
      = throw (InternalError ("Badly formed external primitive " ++ show prim
                                ++ " " ++ show args))

  schDef : {auto c : Ref Ctxt Defs} ->
           Name -> NamedDef -> Core String
  schDef n (MkNmFun args exp)
     = pure $ "(define " ++ schName !(getFullName n) ++ " (lambda (" ++ schArglist args ++ ") "
                      ++ !(schExp 0 exp) ++ "))\n"
  schDef n (MkNmError exp)
     = pure $ "(define (" ++ schName !(getFullName n) ++ " . any-args) " ++ !(schExp 0 exp) ++ ")\n"
  schDef n (MkNmForeign _ _ _) = pure "" -- compiled by specific back end
  schDef n (MkNmCon t a _) = pure "" -- Nothing to compile here

-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
export
getScheme : {auto c : Ref Ctxt Defs} ->
            (schExtPrim : Int -> ExtPrim -> List NamedCExp -> Core String) ->
            (schString : String -> String) ->
            (Name, FC, NamedDef) -> Core String
getScheme schExtPrim schString (n, fc, d)
    = schDef schExtPrim schString n d
