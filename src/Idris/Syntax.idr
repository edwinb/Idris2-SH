module Idris.Syntax

import public Core.Binary
import public Core.Context
import public Core.Core
import public Core.FC
import public Core.Normalise
import public Core.Options
import public Core.TTC
import public Core.TT

import TTImp.TTImp

import Libraries.Data.ANameMap
import Data.List
import Data.Maybe
import Data.String
import Libraries.Data.NameMap
import Libraries.Data.String.Extra
import Libraries.Data.StringMap
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util

import Parser.Lexer.Source

%default covering

public export
data Fixity = InfixL | InfixR | Infix | Prefix

export
Show Fixity where
  show InfixL = "infixl"
  show InfixR = "infixr"
  show Infix  = "infix"
  show Prefix = "prefix"

public export
OpStr : Type
OpStr = Name

mutual
  -- The full high level source language
  -- This gets desugared to RawImp (TTImp.TTImp), then elaborated to
  -- Term (Core.TT)
  public export
  data PTerm : Type where
       -- Direct (more or less) translations to RawImp

       PRef : FC -> Name -> PTerm
       PPi : FC -> RigCount -> PiInfo PTerm -> Maybe Name ->
             (argTy : PTerm) -> (retTy : PTerm) -> PTerm
       PLam : FC -> RigCount -> PiInfo PTerm -> PTerm ->
              (argTy : PTerm) -> (scope : PTerm) -> PTerm
       PLet : FC -> RigCount -> (pat : PTerm) ->
              (nTy : PTerm) -> (nVal : PTerm) -> (scope : PTerm) ->
              (alts : List PClause) -> PTerm
       PCase : FC -> PTerm -> List PClause -> PTerm
       PLocal : FC -> List PDecl -> (scope : PTerm) -> PTerm
       PUpdate : FC -> List PFieldUpdate -> PTerm
       PApp : FC -> PTerm -> PTerm -> PTerm
       PWithApp : FC -> PTerm -> PTerm -> PTerm
       PNamedApp : FC -> PTerm -> Name -> PTerm -> PTerm
       PAutoApp : FC -> PTerm -> PTerm -> PTerm

       PDelayed : FC -> LazyReason -> PTerm -> PTerm
       PDelay : FC -> PTerm -> PTerm
       PForce : FC -> PTerm -> PTerm

       PSearch : FC -> (depth : Nat) -> PTerm
       PPrimVal : FC -> Constant -> PTerm
       PQuote : FC -> PTerm -> PTerm
       PQuoteName : FC -> Name -> PTerm
       PQuoteDecl : FC -> List PDecl -> PTerm
       PUnquote : FC -> PTerm -> PTerm
       PRunElab : FC -> PTerm -> PTerm
       PHole : FC -> (bracket : Bool) -> (holename : String) -> PTerm
       PType : FC -> PTerm
       PAs : FC -> (nameFC : FC) -> Name -> (pattern : PTerm) -> PTerm
       PDotted : FC -> PTerm -> PTerm
       PImplicit : FC -> PTerm
       PInfer : FC -> PTerm

       -- Operators

       POp : (full, opFC : FC) -> OpStr -> PTerm -> PTerm -> PTerm
       PPrefixOp : (full, opFC : FC) -> OpStr -> PTerm -> PTerm
       PSectionL : (full, opFC : FC) -> OpStr -> PTerm -> PTerm
       PSectionR : (full, opFC : FC) -> PTerm -> OpStr -> PTerm
       PEq : FC -> PTerm -> PTerm -> PTerm
       PBracketed : FC -> PTerm -> PTerm

       -- Syntactic sugar
       PString : FC -> List PStr -> PTerm
       PMultiline : FC -> (indent : Nat) -> List (List PStr) -> PTerm
       PDoBlock : FC -> Maybe Namespace -> List PDo -> PTerm
       PBang : FC -> PTerm -> PTerm
       PIdiom : FC -> PTerm -> PTerm
       PList : (full, nilFC : FC) -> List (FC, PTerm) -> PTerm
                                        -- ^   v location of the conses/snocs
       PSnocList : (full, nilFC : FC) -> List ((FC, PTerm)) -> PTerm
       PPair : FC -> PTerm -> PTerm -> PTerm
       PDPair : (full, opFC : FC) -> PTerm -> PTerm -> PTerm -> PTerm
       PUnit : FC -> PTerm
       PIfThenElse : FC -> PTerm -> PTerm -> PTerm -> PTerm
       PComprehension : FC -> PTerm -> List PDo -> PTerm
       PRewrite : FC -> PTerm -> PTerm -> PTerm
       -- A list range  [x,y..z]
       PRange : FC -> PTerm -> Maybe PTerm -> PTerm -> PTerm
       -- A stream range [x,y..]
       PRangeStream : FC -> PTerm -> Maybe PTerm -> PTerm
       -- r.x.y
       PPostfixApp : FC -> PTerm -> List (FC, Name) -> PTerm
       -- .x.y
       PPostfixAppPartial : FC -> List (FC, Name) -> PTerm

       -- Debugging
       PUnifyLog : FC -> LogLevel -> PTerm -> PTerm

       -- with-disambiguation
       PWithUnambigNames : FC -> List Name -> PTerm -> PTerm

  export
  getPTermLoc : PTerm -> FC
  getPTermLoc (PRef fc _) = fc
  getPTermLoc (PPi fc _ _ _ _ _) = fc
  getPTermLoc (PLam fc _ _ _ _ _) = fc
  getPTermLoc (PLet fc _ _ _ _ _ _) = fc
  getPTermLoc (PCase fc _ _) = fc
  getPTermLoc (PLocal fc _ _) = fc
  getPTermLoc (PUpdate fc _) = fc
  getPTermLoc (PApp fc _ _) = fc
  getPTermLoc (PWithApp fc _ _) = fc
  getPTermLoc (PAutoApp fc _ _) = fc
  getPTermLoc (PNamedApp fc _ _ _) = fc
  getPTermLoc (PDelayed fc _ _) = fc
  getPTermLoc (PDelay fc _) = fc
  getPTermLoc (PForce fc _) = fc
  getPTermLoc (PSearch fc _) = fc
  getPTermLoc (PPrimVal fc _) = fc
  getPTermLoc (PQuote fc _) = fc
  getPTermLoc (PQuoteName fc _) = fc
  getPTermLoc (PQuoteDecl fc _) = fc
  getPTermLoc (PUnquote fc _) = fc
  getPTermLoc (PRunElab fc _) = fc
  getPTermLoc (PHole fc _ _) = fc
  getPTermLoc (PType fc) = fc
  getPTermLoc (PAs fc _  _ _) = fc
  getPTermLoc (PDotted fc _) = fc
  getPTermLoc (PImplicit fc) = fc
  getPTermLoc (PInfer fc) = fc
  getPTermLoc (POp fc _ _ _ _) = fc
  getPTermLoc (PPrefixOp fc _ _ _) = fc
  getPTermLoc (PSectionL fc _ _ _) = fc
  getPTermLoc (PSectionR fc _ _ _) = fc
  getPTermLoc (PEq fc _ _) = fc
  getPTermLoc (PBracketed fc _) = fc
  getPTermLoc (PString fc _) = fc
  getPTermLoc (PMultiline fc _ _) = fc
  getPTermLoc (PDoBlock fc _ _) = fc
  getPTermLoc (PBang fc _) = fc
  getPTermLoc (PIdiom fc _) = fc
  getPTermLoc (PList fc _ _) = fc
  getPTermLoc (PSnocList fc _ _) = fc
  getPTermLoc (PPair fc _ _) = fc
  getPTermLoc (PDPair fc _ _ _ _) = fc
  getPTermLoc (PUnit fc) = fc
  getPTermLoc (PIfThenElse fc _ _ _) = fc
  getPTermLoc (PComprehension fc _ _) = fc
  getPTermLoc (PRewrite fc _ _) = fc
  getPTermLoc (PRange fc _ _ _) = fc
  getPTermLoc (PRangeStream fc _ _) = fc
  getPTermLoc (PPostfixApp fc _ _) = fc
  getPTermLoc (PPostfixAppPartial fc _) = fc
  getPTermLoc (PUnifyLog fc _ _) = fc
  getPTermLoc (PWithUnambigNames fc _ _) = fc

  public export
  data PFieldUpdate : Type where
       PSetField : (path : List String) -> PTerm -> PFieldUpdate
       PSetFieldApp : (path : List String) -> PTerm -> PFieldUpdate

  public export
  data PDo : Type where
       DoExp : FC -> PTerm -> PDo
       DoBind : FC -> (nameFC : FC) -> Name -> PTerm -> PDo
       DoBindPat : FC -> PTerm -> PTerm -> List PClause -> PDo
       DoLet : FC -> (lhs : FC) -> Name -> RigCount -> PTerm -> PTerm -> PDo
       DoLetPat : FC -> PTerm -> PTerm -> PTerm -> List PClause -> PDo
       DoLetLocal : FC -> List PDecl -> PDo
       DoRewrite : FC -> PTerm -> PDo

  public export
  data PStr : Type where
       StrLiteral : FC -> String -> PStr
       StrInterp : FC -> PTerm -> PStr

  export
  getLoc : PDo -> FC
  getLoc (DoExp fc _) = fc
  getLoc (DoBind fc _ _ _) = fc
  getLoc (DoBindPat fc _ _ _) = fc
  getLoc (DoLet fc _ _ _ _ _) = fc
  getLoc (DoLetPat fc _ _ _ _) = fc
  getLoc (DoLetLocal fc _) = fc
  getLoc (DoRewrite fc _) = fc

  export
  papply : FC -> PTerm -> List PTerm -> PTerm
  papply fc f [] = f
  papply fc f (a :: as) = papply fc (PApp fc f a) as

  public export
  data PTypeDecl : Type where
       MkPTy : FC -> (nameFC : FC) -> (n : Name) -> (doc: String) -> (type : PTerm) -> PTypeDecl

  export
  getPTypeDeclLoc : PTypeDecl -> FC
  getPTypeDeclLoc (MkPTy fc _ _ _ _) = fc

  public export
  data PDataDecl : Type where
       MkPData : FC -> (tyname : Name) -> (tycon : PTerm) ->
                 (opts : List DataOpt) ->
                 (datacons : List PTypeDecl) -> PDataDecl
       MkPLater : FC -> (tyname : Name) -> (tycon : PTerm) -> PDataDecl

  export
  getPDataDeclLoc : PDataDecl -> FC
  getPDataDeclLoc (MkPData fc _ _ _ _) = fc
  getPDataDeclLoc (MkPLater fc _ _) = fc

  public export
  data PClause : Type where
       MkPatClause : FC -> (lhs : PTerm) -> (rhs : PTerm) ->
                     (whereblock : List PDecl) -> PClause
       MkWithClause : FC -> (lhs : PTerm) ->
                      (wval : PTerm) -> (prf : Maybe Name) ->
                      List WithFlag -> List PClause -> PClause
       MkImpossible : FC -> (lhs : PTerm) -> PClause

  export
  getPClauseLoc : PClause -> FC
  getPClauseLoc (MkPatClause fc _ _ _) = fc
  getPClauseLoc (MkWithClause fc _ _ _ _ _) = fc
  getPClauseLoc (MkImpossible fc _) = fc

  public export
  data Directive : Type where
       Hide : Name -> Directive
       Logging : Maybe LogLevel -> Directive
       LazyOn : Bool -> Directive
       UnboundImplicits : Bool -> Directive
       AmbigDepth : Nat -> Directive
       PairNames : Name -> Name -> Name -> Directive
       RewriteName : Name -> Name -> Directive
       PrimInteger : Name -> Directive
       PrimString : Name -> Directive
       PrimChar : Name -> Directive
       PrimDouble : Name -> Directive
       CGAction : String -> String -> Directive
       Names : Name -> List String -> Directive
       StartExpr : PTerm -> Directive
       Overloadable : Name -> Directive
       Extension : LangExt -> Directive
       DefaultTotality : TotalReq -> Directive
       PrefixRecordProjections : Bool -> Directive
       AutoImplicitDepth : Nat -> Directive
       NFMetavarThreshold : Nat -> Directive
       SearchTimeout : Integer -> Directive
       PatternSynonym : Name -> Directive

  public export
  data PField : Type where
       MkField : FC -> (doc : String) -> RigCount -> PiInfo PTerm ->
                 Name -> (ty : PTerm) -> PField

  -- For noting the pass we're in when desugaring a mutual block
  -- TODO: Decide whether we want mutual blocks!
  public export
  data Pass = Single | AsType | AsDef

  export
  Eq Pass where
    Single == Single = True
    AsType == AsType = True
    AsDef == AsDef = True
    _ == _ = False

  export
  typePass : Pass -> Bool
  typePass p = p == Single || p == AsType

  export
  defPass : Pass -> Bool
  defPass p = p == Single || p == AsDef

  public export
  data PFnOpt : Type where
       IFnOpt : FnOpt -> PFnOpt
       PForeign : List PTerm -> PFnOpt

  public export
  data PDecl : Type where
       PClaim : FC -> RigCount -> Visibility -> List PFnOpt -> PTypeDecl -> PDecl
       PDef : FC -> List PClause -> PDecl
       PData : FC -> (doc : String) -> Visibility -> PDataDecl -> PDecl
       PParameters : FC -> List (Name, RigCount, PiInfo PTerm, PTerm) -> List PDecl -> PDecl
       PUsing : FC -> List (Maybe Name, PTerm) -> List PDecl -> PDecl
       PReflect : FC -> PTerm -> PDecl
       PInterface : FC ->
                    Visibility ->
                    (constraints : List (Maybe Name, PTerm)) ->
                    Name ->
                    (doc : String) ->
                    (params : List (Name, (RigCount, PTerm))) ->
                    (det : List Name) ->
                    (conName : Maybe Name) ->
                    List PDecl ->
                    PDecl
       PImplementation : FC ->
                         Visibility -> List PFnOpt -> Pass ->
                         (implicits : List (Name, RigCount, PTerm)) ->
                         (constraints : List (Maybe Name, PTerm)) ->
                         Name ->
                         (params : List PTerm) ->
                         (implName : Maybe Name) ->
                         (nusing : List Name) ->
                         Maybe (List PDecl) ->
                         PDecl
       PRecord : FC ->
                 (doc : String) ->
                 Visibility ->
                 Name ->
                 (params : List (Name, RigCount, PiInfo PTerm, PTerm)) ->
                 (conName : Maybe Name) ->
                 List PField ->
                 PDecl

       -- TODO: PPostulate
       -- TODO: POpen (for opening named interfaces)
       PMutual : FC -> List PDecl -> PDecl
       PFixity : FC -> Fixity -> Nat -> OpStr -> PDecl
       PNamespace : FC -> Namespace -> List PDecl -> PDecl
       PTransform : FC -> String -> PTerm -> PTerm -> PDecl
       PRunElabDecl : FC -> PTerm -> PDecl
       PDirective : FC -> Directive -> PDecl
       PBuiltin : FC -> BuiltinType -> Name -> PDecl

  export
  getPDeclLoc : PDecl -> FC
  getPDeclLoc (PClaim fc _ _ _ _) = fc
  getPDeclLoc (PDef fc _) = fc
  getPDeclLoc (PData fc _ _ _) = fc
  getPDeclLoc (PParameters fc _ _) = fc
  getPDeclLoc (PUsing fc _ _) = fc
  getPDeclLoc (PReflect fc _) = fc
  getPDeclLoc (PInterface fc _ _ _ _ _ _ _ _) = fc
  getPDeclLoc (PImplementation fc _ _ _ _ _ _ _ _ _ _) = fc
  getPDeclLoc (PRecord fc _ _ _ _ _ _) = fc
  getPDeclLoc (PMutual fc _) = fc
  getPDeclLoc (PFixity fc _ _ _) = fc
  getPDeclLoc (PNamespace fc _ _) = fc
  getPDeclLoc (PTransform fc _ _ _) = fc
  getPDeclLoc (PRunElabDecl fc _) = fc
  getPDeclLoc (PDirective fc _) = fc
  getPDeclLoc (PBuiltin fc _ _) = fc

export
isStrInterp : PStr -> Maybe FC
isStrInterp (StrInterp fc _) = Just fc
isStrInterp (StrLiteral _ _) = Nothing

export
isPDef : PDecl -> Maybe (FC, List PClause)
isPDef (PDef annot cs) = Just (annot, cs)
isPDef _ = Nothing


definedInData : PDataDecl -> List Name
definedInData (MkPData _ n _ _ cons) = n :: map getName cons
  where
    getName : PTypeDecl -> Name
    getName (MkPTy _ _ n _ _) = n
definedInData (MkPLater _ n _) = [n]

export
definedIn : List PDecl -> List Name
definedIn [] = []
definedIn (PClaim _ _ _ _ (MkPTy _ _ n _ _) :: ds) = n :: definedIn ds
definedIn (PData _ _ _ d :: ds) = definedInData d ++ definedIn ds
definedIn (PParameters _ _ pds :: ds) = definedIn pds ++ definedIn ds
definedIn (PUsing _ _ pds :: ds) = definedIn pds ++ definedIn ds
definedIn (PNamespace _ _ ns :: ds) = definedIn ns ++ definedIn ds
definedIn (_ :: ds) = definedIn ds

public export
data REPLEval : Type where
     EvalTC : REPLEval -- Evaluate as if part of the typechecker
     NormaliseAll : REPLEval -- Normalise everything (default)
     Execute : REPLEval -- Evaluate then pass to an executer

export
Show REPLEval where
  show EvalTC = "typecheck"
  show NormaliseAll = "normalise"
  show Execute = "execute"

export
Pretty REPLEval where
  pretty EvalTC = pretty "typecheck"
  pretty NormaliseAll = pretty "normalise"
  pretty Execute = pretty "execute"

public export
data REPLOpt : Type where
     ShowImplicits : Bool -> REPLOpt
     ShowNamespace : Bool -> REPLOpt
     ShowTypes : Bool -> REPLOpt
     EvalMode : REPLEval -> REPLOpt
     Editor : String -> REPLOpt
     CG : String -> REPLOpt
     Profile : Bool -> REPLOpt

export
Show REPLOpt where
  show (ShowImplicits impl) = "showimplicits = " ++ show impl
  show (ShowNamespace ns) = "shownamespace = " ++ show ns
  show (ShowTypes typs) = "showtypes = " ++ show typs
  show (EvalMode mod) = "eval = " ++ show mod
  show (Editor editor) = "editor = " ++ show editor
  show (CG str) = "cg = " ++ str
  show (Profile p) = "profile = " ++ show p

export
Pretty REPLOpt where
  pretty (ShowImplicits impl) = pretty "showimplicits" <++> equals <++> pretty impl
  pretty (ShowNamespace ns) = pretty "shownamespace" <++> equals <++> pretty ns
  pretty (ShowTypes typs) = pretty "showtypes" <++> equals <++> pretty typs
  pretty (EvalMode mod) = pretty "eval" <++> equals <++> pretty mod
  pretty (Editor editor) = pretty "editor" <++> equals <++> pretty editor
  pretty (CG str) = pretty "cg" <++> equals <++> pretty str
  pretty (Profile p) = pretty "profile" <++> equals <++> pretty p

public export
data EditCmd : Type where
     TypeAt : Int -> Int -> Name -> EditCmd
     CaseSplit : Bool -> Int -> Int -> Name -> EditCmd
     AddClause : Bool -> Int -> Name -> EditCmd
     ExprSearch : Bool -> Int -> Name -> List Name -> EditCmd
     ExprSearchNext : EditCmd
     GenerateDef : Bool -> Int -> Name -> Nat -> EditCmd
     GenerateDefNext : EditCmd
     MakeLemma : Bool -> Int -> Name -> EditCmd
     MakeCase : Bool -> Int -> Name -> EditCmd
     MakeWith : Bool -> Int -> Name -> EditCmd

public export
data REPLCmd : Type where
     NewDefn : List PDecl -> REPLCmd
     Eval : PTerm -> REPLCmd
     Check : PTerm -> REPLCmd
     CheckWithImplicits : PTerm -> REPLCmd
     PrintDef : Name -> REPLCmd
     Reload : REPLCmd
     Load : String -> REPLCmd
     ImportMod : ModuleIdent -> REPLCmd
     Edit : REPLCmd
     Compile : PTerm -> String -> REPLCmd
     Exec : PTerm -> REPLCmd
     Help : REPLCmd
     TypeSearch : PTerm -> REPLCmd
     FuzzyTypeSearch : PTerm -> REPLCmd
     DebugInfo : Name -> REPLCmd
     SetOpt : REPLOpt -> REPLCmd
     GetOpts : REPLCmd
     CGDirective : String -> REPLCmd
     CD : String -> REPLCmd
     CWD: REPLCmd
     Missing : Name -> REPLCmd
     Total : Name -> REPLCmd
     Doc : PTerm -> REPLCmd
     Browse : Namespace -> REPLCmd
     SetLog : Maybe LogLevel -> REPLCmd
     SetConsoleWidth : Maybe Nat -> REPLCmd
     SetColor : Bool -> REPLCmd
     Metavars : REPLCmd
     Editing : EditCmd -> REPLCmd
     RunShellCommand : String -> REPLCmd
     ShowVersion : REPLCmd
     Quit : REPLCmd
     NOP : REPLCmd
     ImportPackage : String -> REPLCmd

public export
record Import where
  constructor MkImport
  loc : FC
  reexport : Bool
  path : ModuleIdent
  nameAs : Namespace

public export
record Module where
  constructor MkModule
  headerLoc : FC
  moduleNS : ModuleIdent
  imports : List Import
  documentation : String
  decls : List PDecl

mutual
  showAlt : PClause -> String
  showAlt (MkPatClause _ lhs rhs _) = " | " ++ show lhs ++ " => " ++ show rhs ++ ";"
  showAlt (MkWithClause _ lhs wval prf flags cs) = " | <<with alts not possible>>;"
  showAlt (MkImpossible _ lhs) = " | " ++ show lhs ++ " impossible;"

  showDo : PDo -> String
  showDo (DoExp _ tm) = show tm
  showDo (DoBind _ _ n tm) = show n ++ " <- " ++ show tm
  showDo (DoBindPat _ l tm alts)
      = show l ++ " <- " ++ show tm ++ concatMap showAlt alts
  showDo (DoLet _ _ l rig _ tm) = "let " ++ show l ++ " = " ++ show tm
  showDo (DoLetPat _ l _ tm alts)
      = "let " ++ show l ++ " = " ++ show tm ++ concatMap showAlt alts
  showDo (DoLetLocal _ ds)
      -- We'll never see this when displaying a normal form...
      = "let { << definitions >>  }"
  showDo (DoRewrite _ rule)
      = "rewrite " ++ show rule

  export
  Show PStr where
    show (StrLiteral _ str) = show str
    show (StrInterp _ tm) = show tm

  showUpdate : PFieldUpdate -> String
  showUpdate (PSetField p v) = showSep "." p ++ " = " ++ show v
  showUpdate (PSetFieldApp p v) = showSep "." p ++ " $= " ++ show v

  export
  Show PTerm where
    showPrec d (PRef _ n) = showPrec d n
    showPrec d (PPi _ rig Explicit Nothing arg ret)
        = showPrec d arg ++ " -> " ++ showPrec d ret
    showPrec d (PPi _ rig Explicit (Just n) arg ret)
        = "(" ++ showCount rig ++ showPrec d n ++ " : " ++ showPrec d arg ++ ") -> " ++ showPrec d ret
    showPrec d (PPi _ rig Implicit Nothing arg ret) -- shouldn't happen
        = "{" ++ showCount rig ++ "_ : " ++ showPrec d arg ++ "} -> " ++ showPrec d ret
    showPrec d (PPi _ rig Implicit (Just n) arg ret)
        = "{" ++ showCount rig ++ showPrec d n ++ " : " ++ showPrec d arg ++ "} -> " ++ showPrec d ret
    showPrec d (PPi _ top AutoImplicit Nothing arg ret)
        = showPrec d arg ++ " => " ++ showPrec d ret
    showPrec d (PPi _ rig AutoImplicit (Just n) arg ret)
        = "{auto " ++ showCount rig ++ showPrec d n ++ " : " ++ showPrec d arg ++ "} -> " ++ showPrec d ret
    showPrec d (PPi _ rig (DefImplicit t) Nothing arg ret) -- shouldn't happen
        = "{default " ++ showPrec App t ++ " " ++ showCount rig ++ "_ : " ++ showPrec d arg ++ "} -> " ++ showPrec d ret
    showPrec d (PPi _ rig (DefImplicit t) (Just n) arg ret)
        = "{default " ++ showPrec App t ++ " " ++ showCount rig ++ showPrec d n ++ " : " ++ showPrec d arg ++ "} -> " ++ showPrec d ret
    showPrec d (PLam _ rig _ n (PImplicit _) sc)
        = "\\" ++ showCount rig ++ showPrec d n ++ " => " ++ showPrec d sc
    showPrec d (PLam _ rig _ n ty sc)
        = "\\" ++ showCount rig ++ showPrec d n ++ " : " ++ showPrec d ty ++ " => " ++ showPrec d sc
    showPrec d (PLet _ rig n (PImplicit _) val sc alts)
        = "let " ++ showCount rig ++ showPrec d n ++ " = " ++ showPrec d val ++ " in " ++ showPrec d sc
    showPrec d (PLet _ rig n ty val sc alts)
        = "let " ++ showCount rig ++ showPrec d n ++ " : " ++ showPrec d ty ++ " = "
                 ++ showPrec d val ++ concatMap showAlt alts ++
                 " in " ++ showPrec d sc
      where
        showAlt : PClause -> String
        showAlt (MkPatClause _ lhs rhs _) = " | " ++ show lhs ++ " => " ++ show rhs ++ ";"
        showAlt (MkWithClause _ lhs rhs prf flags _) = " | <<with alts not possible>>"
        showAlt (MkImpossible _ lhs) = " | " ++ show lhs ++ " impossible;"
    showPrec _ (PCase _ tm cs)
        = "case " ++ show tm ++ " of { " ++
            showSep " ; " (map showCase cs) ++ " }"
      where
        showCase : PClause -> String
        showCase (MkPatClause _ lhs rhs _) = show lhs ++ " => " ++ show rhs
        showCase (MkWithClause _ lhs rhs _ flags _) = " | <<with alts not possible>>"
        showCase (MkImpossible _ lhs) = show lhs ++ " impossible"
    showPrec d (PLocal _ ds sc) -- We'll never see this when displaying a normal form...
        = "let { << definitions >>  } in " ++ showPrec d sc
    showPrec d (PUpdate _ fs)
        = "record { " ++ showSep ", " (map showUpdate fs) ++ " }"
    showPrec d (PApp _ f a) =
      let catchall : Lazy String := showPrec App f ++ " " ++ showPrec App a in
      case f of
        PRef _ n =>
          if isJust (isRF n)
          then showPrec App a ++ " " ++ showPrec App f
          else catchall
        _ => catchall
    showPrec d (PWithApp _ f a) = showPrec d f ++ " | " ++ showPrec d a
    showPrec d (PAutoApp _ f a)
        = showPrec d f ++ " @{" ++ showPrec d a ++ "}"
    showPrec d (PDelayed _ LInf ty)
        = showCon d "Inf" $ showArg ty
    showPrec d (PDelayed _ _ ty)
        = showCon d "Lazy" $ showArg ty
    showPrec d (PDelay _ tm)
        = showCon d "Delay" $ showArg tm
    showPrec d (PForce _ tm)
        = showCon d "Force" $ showArg tm
    showPrec d (PNamedApp _ f n (PRef _ a))
        = if n == a
             then showPrec d f ++ " {" ++ showPrec d n ++ "}"
             else showPrec d f ++ " {" ++ showPrec d n ++ " = " ++ showPrec d a ++ "}"
    showPrec d (PNamedApp _ f n a)
        = showPrec d f ++ " {" ++ showPrec d n ++ " = " ++ showPrec d a ++ "}"
    showPrec _ (PSearch _ _) = "%search"
    showPrec d (PQuote _ tm) = "`(" ++ showPrec d tm ++ ")"
    showPrec d (PQuoteName _ n) = "`{{" ++ showPrec d n ++ "}}"
    showPrec d (PQuoteDecl _ tm) = "`[ <<declaration>> ]"
    showPrec d (PUnquote _ tm) = "~(" ++ showPrec d tm ++ ")"
    showPrec d (PRunElab _ tm) = "%runElab " ++ showPrec d tm
    showPrec d (PPrimVal _ c) = showPrec d c
    showPrec _ (PHole _ _ n) = "?" ++ n
    showPrec _ (PType _) = "Type"
    showPrec d (PAs _ _ n p) = showPrec d n ++ "@" ++ showPrec d p
    showPrec d (PDotted _ p) = "." ++ showPrec d p
    showPrec _ (PImplicit _) = "_"
    showPrec _ (PInfer _) = "?"
    showPrec d (POp _ _ op x y) = showPrec d x ++ " " ++ showPrecOp d op ++ " " ++ showPrec d y
    showPrec d (PPrefixOp _ _ op x) = showPrec d op ++ showPrec d x
    showPrec d (PSectionL _ _ op x) = "(" ++ showPrecOp d op ++ " " ++ showPrec d x ++ ")"
    showPrec d (PSectionR _ _ x op) = "(" ++ showPrec d x ++ " " ++ showPrecOp d op ++ ")"
    showPrec d (PEq fc l r) = showPrec d l ++ " = " ++ showPrec d r
    showPrec d (PBracketed _ tm) = "(" ++ showPrec d tm ++ ")"
    showPrec d (PString _ xs) = join " ++ " $ show <$> xs
    showPrec d (PMultiline _ indent xs) = "multiline (" ++ (join " ++ " $ show <$> concat xs) ++ ")"
    showPrec d (PDoBlock _ ns ds)
        = "do " ++ showSep " ; " (map showDo ds)
    showPrec d (PBang _ tm) = "!" ++ showPrec d tm
    showPrec d (PIdiom _ tm) = "[|" ++ showPrec d tm ++ "|]"
    showPrec d (PList _ _ xs)
        = "[" ++ showSep ", " (map (showPrec d . snd) xs) ++ "]"
    showPrec d (PSnocList _ _ xs)
        = "[<" ++ showSep ", " (map (showPrec d . snd) xs) ++ "]"
    showPrec d (PPair _ l r) = "(" ++ showPrec d l ++ ", " ++ showPrec d r ++ ")"
    showPrec d (PDPair _ _ l (PImplicit _) r) = "(" ++ showPrec d l ++ " ** " ++ showPrec d r ++ ")"
    showPrec d (PDPair _ _ l ty r) = "(" ++ showPrec d l ++ " : " ++ showPrec d ty ++
                                 " ** " ++ showPrec d r ++ ")"
    showPrec _ (PUnit _) = "()"
    showPrec d (PIfThenElse _ x t e) = "if " ++ showPrec d x ++ " then " ++ showPrec d t ++
                                 " else " ++ showPrec d e
    showPrec d (PComprehension _ ret es)
        = "[" ++ showPrec d (dePure ret) ++ " | " ++
                 showSep ", " (map (showDo . deGuard) es) ++ "]"
      where
        dePure : PTerm -> PTerm
        dePure tm@(PApp _ (PRef _ n) arg)
            = if dropNS n == UN "pure" then arg else tm
        dePure tm = tm

        deGuard : PDo -> PDo
        deGuard tm@(DoExp fc (PApp _ (PRef _ n) arg))
            = if dropNS n == UN "guard" then DoExp fc arg else tm
        deGuard tm = tm
    showPrec d (PRewrite _ rule tm)
        = "rewrite " ++ showPrec d rule ++ " in " ++ showPrec d tm
    showPrec d (PRange _ start Nothing end)
        = "[" ++ showPrec d start ++ " .. " ++ showPrec d end ++ "]"
    showPrec d (PRange _ start (Just next) end)
        = "[" ++ showPrec d start ++ ", " ++ showPrec d next ++ " .. " ++ showPrec d end ++ "]"
    showPrec d (PRangeStream _ start Nothing)
        = "[" ++ showPrec d start ++ " .. ]"
    showPrec d (PRangeStream _ start (Just next))
        = "[" ++ showPrec d start ++ ", " ++ showPrec d next ++ " .. ]"
    showPrec d (PUnifyLog _ _ tm) = showPrec d tm
    showPrec d (PPostfixApp fc rec fields)
        = showPrec d rec ++ concatMap (\n => "." ++ show n) fields
    showPrec d (PPostfixAppPartial fc fields)
        = concatMap (\n => "." ++ show n) fields
    showPrec d (PWithUnambigNames fc ns rhs)
        = "with " ++ show ns ++ " " ++ showPrec d rhs

  showPrecOp : Prec -> OpStr -> String
  showPrecOp d op = if isOpName op
    then        showPrec d op
    else "`" ++ showPrec d op ++ "`"

public export
record Method where
  constructor MkMethod
  name     : Name
  count    : RigCount
  totalReq : Maybe TotalReq
  type     : RawImp

export
Show Method where
  show (MkMethod n c treq ty)
    = "[" ++ show treq ++ "] " ++ show c ++ " " ++ show n ++ " : " ++ show ty

public export
record IFaceInfo where
  constructor MkIFaceInfo
  iconstructor : Name
  implParams : List Name
  params : List Name
  parents : List RawImp
  methods : List Method
     -- ^ name, whether a data method, and desugared type (without constraint)
  defaults : List (Name, List ImpClause)

export
TTC Method where
  toBuf b (MkMethod nm c treq ty)
      = do toBuf b nm
           toBuf b c
           toBuf b treq
           toBuf b ty

  fromBuf b
      = do nm <- fromBuf b
           c <- fromBuf b
           treq <- fromBuf b
           ty <- fromBuf b
           pure (MkMethod nm c treq ty)


export
TTC IFaceInfo where
  toBuf b (MkIFaceInfo ic impps ps cs ms ds)
      = do toBuf b ic
           toBuf b impps
           toBuf b ps
           toBuf b cs
           toBuf b ms
           toBuf b ds

  fromBuf b
      = do ic <- fromBuf b
           impps <- fromBuf b
           ps <- fromBuf b
           cs <- fromBuf b
           ms <- fromBuf b
           ds <- fromBuf b
           pure (MkIFaceInfo ic impps ps cs ms ds)

-- If you update this, update 'extendSyn' in Desugar to keep it up to date
-- when reading imports
public export
record SyntaxInfo where
  constructor MkSyntax
  -- Keep infix/prefix, then we can define operators which are both
  -- (most obviously, -)
  infixes : StringMap (Fixity, Nat)
  prefixes : StringMap Nat
  ifaces : ANameMap IFaceInfo
  saveIFaces : List Name -- interfaces defined in current session, to save
                         -- to ttc
  docstrings : ANameMap String
  saveDocstrings : NameMap () -- names defined in current session
  bracketholes : List Name -- hole names in argument position (so need
                           -- to be bracketed when solved)
  usingImpl : List (Maybe Name, RawImp)
  startExpr : RawImp

export
TTC Fixity where
  toBuf b InfixL = tag 0
  toBuf b InfixR = tag 1
  toBuf b Infix = tag 2
  toBuf b Prefix = tag 3

  fromBuf b
      = case !getTag of
             0 => pure InfixL
             1 => pure InfixR
             2 => pure Infix
             3 => pure Prefix
             _ => corrupt "Fixity"

export
TTC SyntaxInfo where
  toBuf b syn
      = do toBuf b (StringMap.toList (infixes syn))
           toBuf b (StringMap.toList (prefixes syn))
           toBuf b (filter (\n => fst n `elem` saveIFaces syn)
                           (ANameMap.toList (ifaces syn)))
           toBuf b (filter (\n => case lookup (fst n) (saveDocstrings syn) of
                                       Nothing => False
                                       _ => True)
                           (ANameMap.toList (docstrings syn)))
           toBuf b (bracketholes syn)
           toBuf b (startExpr syn)

  fromBuf b
      = do inf <- fromBuf b
           pre <- fromBuf b
           ifs <- fromBuf b
           dstrs <- fromBuf b
           bhs <- fromBuf b
           start <- fromBuf b
           pure (MkSyntax (fromList inf) (fromList pre) (fromList ifs)
                          [] (fromList dstrs) empty bhs [] start)

HasNames IFaceInfo where
  full gam iface
      = do -- coreLift $ printLn (iconstructor iface)
           -- coreLift $ printLn (methods iface)
           pure iface

  resolved gam iface = pure iface

HasNames a => HasNames (ANameMap a) where
  full gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : ANameMap a -> List (Name, a) -> Core (ANameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (addName !(full gam k) !(full gam v) ms) ns

  resolved gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : ANameMap a -> List (Name, a) -> Core (ANameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (addName !(resolved gam k) !(resolved gam v) ms) ns

export
HasNames SyntaxInfo where
  full gam syn
      = pure $ record { ifaces = !(full gam (ifaces syn)),
                        bracketholes = !(traverse (full gam) (bracketholes syn))
                      } syn
  resolved gam syn
      = pure $ record { ifaces = !(resolved gam (ifaces syn)),
                        bracketholes = !(traverse (resolved gam) (bracketholes syn))
                      } syn

export
initSyntax : SyntaxInfo
initSyntax
    = MkSyntax initInfix
               initPrefix
               empty
               []
               initDocStrings
               initSaveDocStrings
               []
               []
               (IVar EmptyFC (UN "main"))

  where

    initInfix : StringMap (Fixity, Nat)
    initInfix = insert "=" (Infix, 0) empty

    initPrefix : StringMap Nat
    initPrefix = fromList
      [ ("-", 10)
      , ("negate", 10) -- for documentation purposes
      ]

    initDocStrings : ANameMap String
    initDocStrings = empty

    initSaveDocStrings : NameMap ()
    initSaveDocStrings = empty

-- A label for Syntax info in the global state
export
data Syn : Type where

export
withSyn : {auto s : Ref Syn SyntaxInfo} -> Core a -> Core a
withSyn = wrapRef Syn (\_ => pure ())

export
mapPTermM : (PTerm -> Core PTerm) -> PTerm -> Core PTerm
mapPTermM f = goPTerm where

  mutual

    goPTerm : PTerm -> Core PTerm
    goPTerm t@(PRef _ _) = f t
    goPTerm (PPi fc x info z argTy retTy) =
      PPi fc x <$> goPiInfo info
               <*> pure z
               <*> goPTerm argTy
               <*> goPTerm retTy
      >>= f
    goPTerm (PLam fc x info z argTy scope) =
      PLam fc x <$> goPiInfo info
                <*> pure z
                <*> goPTerm argTy
                <*> goPTerm scope
      >>= f
    goPTerm (PLet fc x pat nTy nVal scope alts) =
      PLet fc x <$> goPTerm pat
                <*> goPTerm nTy
                <*> goPTerm nVal
                <*> goPTerm scope
                <*> goPClauses alts
      >>= f
    goPTerm (PCase fc x xs) =
      PCase fc <$> goPTerm x
               <*> goPClauses xs
      >>= f
    goPTerm (PLocal fc xs scope) =
      PLocal fc <$> goPDecls xs
                <*> goPTerm scope
      >>= f
    goPTerm (PUpdate fc xs) =
      PUpdate fc <$> goPFieldUpdates xs
      >>= f
    goPTerm (PApp fc x y) =
      PApp fc <$> goPTerm x
              <*> goPTerm y
      >>= f
    goPTerm (PWithApp fc x y) =
      PWithApp fc <$> goPTerm x
                  <*> goPTerm y
      >>= f
    goPTerm (PAutoApp fc x y) =
      PAutoApp fc <$> goPTerm x
                         <*> goPTerm y
      >>= f
    goPTerm (PNamedApp fc x n y) =
      PNamedApp fc <$> goPTerm x
                   <*> pure n
                   <*> goPTerm y
      >>= f
    goPTerm (PDelayed fc x y) =
      PDelayed fc x <$> goPTerm y
      >>= f
    goPTerm (PDelay fc x) =
      PDelay fc <$> goPTerm x
      >>= f
    goPTerm (PForce fc x) =
      PForce fc <$> goPTerm x
      >>= f
    goPTerm t@(PSearch _ _) = f t
    goPTerm t@(PPrimVal _ _) = f t
    goPTerm (PQuote fc x) =
      PQuote fc <$> goPTerm x
      >>= f
    goPTerm t@(PQuoteName _ _) = f t
    goPTerm (PQuoteDecl fc x) =
      PQuoteDecl fc <$> traverse goPDecl x
      >>= f
    goPTerm (PUnquote fc x) =
      PUnquote fc <$> goPTerm x
      >>= f
    goPTerm (PRunElab fc x) =
      PRunElab fc <$> goPTerm x
      >>= f
    goPTerm t@(PHole _ _ _) = f t
    goPTerm t@(PType _) = f t
    goPTerm (PAs fc nameFC x pat) =
      PAs fc nameFC x <$> goPTerm pat
      >>= f
    goPTerm (PDotted fc x) =
      PDotted fc <$> goPTerm x
      >>= f
    goPTerm t@(PImplicit _) = f t
    goPTerm t@(PInfer _) = f t
    goPTerm (POp fc opFC x y z) =
      POp fc opFC x <$> goPTerm y
                    <*> goPTerm z
      >>= f
    goPTerm (PPrefixOp fc opFC x y) =
      PPrefixOp fc opFC x <$> goPTerm y
      >>= f
    goPTerm (PSectionL fc opFC x y) =
      PSectionL fc opFC x <$> goPTerm y
      >>= f
    goPTerm (PSectionR fc opFC x y) =
      PSectionR fc opFC <$> goPTerm x
                   <*> pure y
      >>= f
    goPTerm (PEq fc x y) =
      PEq fc <$> goPTerm x
             <*> goPTerm y
      >>= f
    goPTerm (PBracketed fc x) =
      PBracketed fc <$> goPTerm x
      >>= f
    goPTerm (PString fc xs) =
      PString fc <$> goPStrings xs
      >>= f
    goPTerm (PMultiline fc x ys) =
      PMultiline fc x <$> goPStringLines ys
      >>= f
    goPTerm (PDoBlock fc ns xs) =
      PDoBlock fc ns <$> goPDos xs
      >>= f
    goPTerm (PBang fc x) =
      PBang fc <$> goPTerm x
      >>= f
    goPTerm (PIdiom fc x) =
      PIdiom fc <$> goPTerm x
      >>= f
    goPTerm (PList fc nilFC xs) =
      PList fc nilFC <$> goPairedPTerms xs
      >>= f
    goPTerm (PSnocList fc nilFC xs) =
      PSnocList fc nilFC <$> goPairedPTerms xs
      >>= f
    goPTerm (PPair fc x y) =
      PPair fc <$> goPTerm x
               <*> goPTerm y
      >>= f
    goPTerm (PDPair fc opFC x y z) =
      PDPair fc opFC
                <$> goPTerm x
                <*> goPTerm y
                <*> goPTerm z
      >>= f
    goPTerm t@(PUnit _) = f t
    goPTerm (PIfThenElse fc x y z) =
      PIfThenElse fc <$> goPTerm x
                     <*> goPTerm y
                     <*> goPTerm z
      >>= f
    goPTerm (PComprehension fc x xs) =
      PComprehension fc <$> goPTerm x
                        <*> goPDos xs
      >>= f
    goPTerm (PRewrite fc x y) =
      PRewrite fc <$> goPTerm x
                  <*> goPTerm y
      >>= f
    goPTerm (PRange fc x y z) =
      PRange fc <$> goPTerm x
                <*> goMPTerm y
                <*> goPTerm z
      >>= f
    goPTerm (PRangeStream fc x y) =
      PRangeStream fc <$> goPTerm x
                      <*> goMPTerm y
      >>= f
    goPTerm (PUnifyLog fc k x) =
      PUnifyLog fc k <$> goPTerm x
      >>= f
    goPTerm (PPostfixApp fc rec fields) =
      PPostfixApp fc <$> goPTerm rec <*> pure fields
      >>= f
    goPTerm (PPostfixAppPartial fc fields) =
      f (PPostfixAppPartial fc fields)
    goPTerm (PWithUnambigNames fc ns rhs) =
      PWithUnambigNames fc ns <$> goPTerm rhs
      >>= f

    goPFieldUpdate : PFieldUpdate -> Core PFieldUpdate
    goPFieldUpdate (PSetField p t)    = PSetField p <$> goPTerm t
    goPFieldUpdate (PSetFieldApp p t) = PSetFieldApp p <$> goPTerm t

    goPStr : PStr -> Core PStr
    goPStr (StrInterp fc t) = StrInterp fc <$> goPTerm t
    goPStr x                = pure x

    goPDo : PDo -> Core PDo
    goPDo (DoExp fc t) = DoExp fc <$> goPTerm t
    goPDo (DoBind fc nameFC n t) = DoBind fc nameFC n <$> goPTerm t
    goPDo (DoBindPat fc t u cls) =
      DoBindPat fc <$> goPTerm t
                   <*> goPTerm u
                   <*> goPClauses cls
    goPDo (DoLet fc lhsFC n c t scope) =
       DoLet fc lhsFC n c <$> goPTerm t
                          <*> goPTerm scope
    goPDo (DoLetPat fc pat t scope cls) =
       DoLetPat fc <$> goPTerm pat
                   <*> goPTerm t
                   <*> goPTerm scope
                   <*> goPClauses cls
    goPDo (DoLetLocal fc decls) = DoLetLocal fc <$> goPDecls decls
    goPDo (DoRewrite fc t) = DoRewrite fc <$> goPTerm t

    goPClause : PClause -> Core PClause
    goPClause (MkPatClause fc lhs rhs wh) =
      MkPatClause fc <$> goPTerm lhs
                     <*> goPTerm rhs
                     <*> goPDecls wh
    goPClause (MkWithClause fc lhs wVal prf flags cls) =
      MkWithClause fc <$> goPTerm lhs
                      <*> goPTerm wVal
                      <*> pure prf
                      <*> pure flags
                      <*> goPClauses cls
    goPClause (MkImpossible fc lhs) = MkImpossible fc <$> goPTerm lhs

    goPDecl : PDecl -> Core PDecl
    goPDecl (PClaim fc c v opts tdecl) =
      PClaim fc c v <$> goPFnOpts opts
                    <*> goPTypeDecl tdecl
    goPDecl (PDef fc cls) = PDef fc <$> goPClauses cls
    goPDecl (PData fc doc v d) = PData fc doc v <$> goPDataDecl d
    goPDecl (PParameters fc nts ps) =
      PParameters fc <$> go4TupledPTerms nts
                     <*> goPDecls ps
    goPDecl (PUsing fc mnts ps) =
      PUsing fc <$> goPairedPTerms mnts
                <*> goPDecls ps
    goPDecl (PReflect fc t) = PReflect fc <$> goPTerm t
    goPDecl (PInterface fc v mnts n doc nrts ns mn ps) =
      PInterface fc v <$> goPairedPTerms mnts
                      <*> pure n
                      <*> pure doc
                      <*> go3TupledPTerms nrts
                      <*> pure ns
                      <*> pure mn
                      <*> goPDecls ps
    goPDecl (PImplementation fc v opts p is cs n ts mn ns mps) =
      PImplementation fc v opts p <$> go3TupledPTerms is
                                  <*> goPairedPTerms cs
                                  <*> pure n
                                  <*> goPTerms ts
                                  <*> pure mn
                                  <*> pure ns
                                  <*> goMPDecls mps
    goPDecl (PRecord fc doc v n nts mn fs) =
      PRecord fc doc v n <$> go4TupledPTerms nts
                         <*> pure mn
                         <*> goPFields fs
    goPDecl (PMutual fc ps) = PMutual fc <$> goPDecls ps
    goPDecl p@(PFixity _ _ _ _) = pure p
    goPDecl (PNamespace fc strs ps) = PNamespace fc strs <$> goPDecls ps
    goPDecl (PTransform fc n a b) = PTransform fc n <$> goPTerm a <*> goPTerm b
    goPDecl (PRunElabDecl fc a) = PRunElabDecl fc <$> goPTerm a
    goPDecl p@(PDirective _ _) = pure p
    goPDecl p@(PBuiltin _ _ _) = pure p


    goPTypeDecl : PTypeDecl -> Core PTypeDecl
    goPTypeDecl (MkPTy fc nameFC n d t) = MkPTy fc nameFC n d <$> goPTerm t

    goPDataDecl : PDataDecl -> Core PDataDecl
    goPDataDecl (MkPData fc n t opts tdecls) =
      MkPData fc n <$> goPTerm t
                   <*> pure opts
                   <*> goPTypeDecls tdecls
    goPDataDecl (MkPLater fc n t) = MkPLater fc n <$> goPTerm t

    goPField : PField -> Core PField
    goPField (MkField fc doc c info n t) =
      MkField fc doc c <$> goPiInfo info
                       <*> pure n
                       <*> goPTerm t

    goPiInfo : PiInfo PTerm -> Core (PiInfo PTerm)
    goPiInfo (DefImplicit t) = DefImplicit <$> goPTerm t
    goPiInfo t = pure t

    goPFnOpt : PFnOpt -> Core PFnOpt
    goPFnOpt o@(IFnOpt _) = pure o
    goPFnOpt (PForeign ts) = PForeign <$> goPTerms ts

    -- Traversable stuff. Inlined for termination checking.

    goMPTerm : Maybe PTerm -> Core (Maybe PTerm)
    goMPTerm Nothing  = pure Nothing
    goMPTerm (Just t) = Just <$> goPTerm t

    goPTerms : List PTerm -> Core (List PTerm)
    goPTerms []        = pure []
    goPTerms (t :: ts) = (::) <$> goPTerm t <*> goPTerms ts

    goPairedPTerms : List (a, PTerm) -> Core (List (a, PTerm))
    goPairedPTerms []             = pure []
    goPairedPTerms ((a, t) :: ts) =
       (::) . MkPair a <$> goPTerm t
                       <*> goPairedPTerms ts

    go3TupledPTerms : List (a, b, PTerm) -> Core (List (a, b, PTerm))
    go3TupledPTerms [] = pure []
    go3TupledPTerms ((a, b, t) :: ts) =
      (::) . (\ c => (a, b, c)) <$> goPTerm t
                                <*> go3TupledPTerms ts

    go4TupledPTerms : List (a, b, PiInfo PTerm, PTerm) -> Core (List (a, b, PiInfo PTerm, PTerm))
    go4TupledPTerms [] = pure []
    go4TupledPTerms ((a, b, p, t) :: ts) =
      (\ p, d, ts => (a, b, p, d) :: ts) <$> goPiInfo p
                                         <*> goPTerm t
                                         <*> go4TupledPTerms ts

    goPStringLines : List (List PStr) -> Core (List (List PStr))
    goPStringLines []        = pure []
    goPStringLines (line :: lines) = (::) <$> goPStrings line <*> goPStringLines lines

    goPStrings : List PStr -> Core (List PStr)
    goPStrings []        = pure []
    goPStrings (str :: strs) = (::) <$> goPStr str <*> goPStrings strs

    goPDos : List PDo -> Core (List PDo)
    goPDos []        = pure []
    goPDos (d :: ds) = (::) <$> goPDo d <*> goPDos ds

    goPClauses : List PClause -> Core (List PClause)
    goPClauses []          = pure []
    goPClauses (cl :: cls) = (::) <$> goPClause cl <*> goPClauses cls

    goMPDecls : Maybe (List PDecl) -> Core (Maybe (List PDecl))
    goMPDecls Nothing   = pure Nothing
    goMPDecls (Just ps) = Just <$> goPDecls ps

    goPDecls : List PDecl -> Core (List PDecl)
    goPDecls []          = pure []
    goPDecls (d :: ds) = (::) <$> goPDecl d <*> goPDecls ds

    goPFieldUpdates : List PFieldUpdate -> Core (List PFieldUpdate)
    goPFieldUpdates []          = pure []
    goPFieldUpdates (fu :: fus) = (::) <$> goPFieldUpdate fu <*> goPFieldUpdates fus

    goPFields : List PField -> Core (List PField)
    goPFields []        = pure []
    goPFields (f :: fs) = (::) <$> goPField f <*> goPFields fs

    goPFnOpts : List PFnOpt -> Core (List PFnOpt)
    goPFnOpts []        = pure []
    goPFnOpts (o :: os) = (::) <$> goPFnOpt o <*> goPFnOpts os

    goPTypeDecls : List PTypeDecl -> Core (List PTypeDecl)
    goPTypeDecls []        = pure []
    goPTypeDecls (t :: ts) = (::) <$> goPTypeDecl t <*> goPTypeDecls ts
