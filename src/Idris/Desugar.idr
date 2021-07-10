module Idris.Desugar

import Core.Binary
import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Options
import Core.Pattern
import Core.TT
import Core.Unify

import Data.Maybe

import Libraries.Data.List.Extra
import Libraries.Data.StringMap
import Libraries.Data.String.Extra
import Libraries.Data.ANameMap

import Idris.Doc.String
import Idris.Syntax

import Idris.Elab.Implementation
import Idris.Elab.Interface

import Idris.Desugar.Mutual

import Parser.Lexer.Source

import TTImp.BindImplicits
import TTImp.Parser
import TTImp.TTImp
import TTImp.Utils

import Libraries.Data.IMaybe
import Libraries.Utils.Shunting
import Libraries.Utils.String

import Control.Monad.State
import Data.Maybe
import Data.List
import Data.List.Views
import Data.List1
import Data.String
import Libraries.Data.String.Extra

%hide Data.String.lines
%hide Data.String.lines'
%hide Data.String.unlines
%hide Data.String.unlines'

-- Convert high level Idris declarations (PDecl from Idris.Syntax) into
-- TTImp, recording any high level syntax info on the way (e.g. infix
-- operators)

-- Desugaring from high level Idris syntax to TTImp involves:

-- * Shunting infix operators into function applications according to precedence
-- * Replacing 'do' notating with applications of (>>=)
-- * Replacing string interpolation with concatenation by (++)
-- * Replacing pattern matching binds with 'case'
-- * Changing tuples to 'Pair/MkPair'
-- * List notation
-- * Replacing !-notation
-- * Dependent pair notation
-- * Idiom brackets

%default covering

public export
data Side = LHS | AnyExpr

export
Eq Side where
  LHS == LHS = True
  AnyExpr == AnyExpr = True
  _ == _ = False

export
extendSyn : {auto s : Ref Syn SyntaxInfo} ->
            SyntaxInfo -> Core ()
extendSyn newsyn
    = do syn <- get Syn
         put Syn (record { infixes $= mergeLeft (infixes newsyn),
                           prefixes $= mergeLeft (prefixes newsyn),
                           ifaces $= merge (ifaces newsyn),
                           docstrings $= merge (docstrings newsyn),
                           bracketholes $= ((bracketholes newsyn) ++) }
                  syn)

mkPrec : Fixity -> Nat -> OpPrec
mkPrec InfixL p = AssocL p
mkPrec InfixR p = AssocR p
mkPrec Infix p = NonAssoc p
mkPrec Prefix p = Prefix p

toTokList : {auto s : Ref Syn SyntaxInfo} ->
            PTerm -> Core (List (Tok OpStr PTerm))
toTokList (POp fc opFC opn l r)
    = do syn <- get Syn
         let op = nameRoot opn
         case lookup op (infixes syn) of
              Nothing =>
                  if any isOpChar (fastUnpack op)
                     then throw (GenericMsg fc $ "Unknown operator '" ++ op ++ "'")
                     else do rtoks <- toTokList r
                             pure (Expr l :: Op fc opFC opn backtickPrec :: rtoks)
              Just (Prefix, _) =>
                      throw (GenericMsg fc $ "'" ++ op ++ "' is a prefix operator")
              Just (fix, prec) =>
                   do rtoks <- toTokList r
                      pure (Expr l :: Op fc opFC opn (mkPrec fix prec) :: rtoks)
  where
    backtickPrec : OpPrec
    backtickPrec = NonAssoc 1
toTokList (PPrefixOp fc opFC opn arg)
    = do syn <- get Syn
         let op = nameRoot opn
         case lookup op (prefixes syn) of
              Nothing =>
                   throw (GenericMsg fc $ "'" ++ op ++ "' is not a prefix operator")
              Just prec =>
                   do rtoks <- toTokList arg
                      pure (Op fc opFC opn (Prefix prec) :: rtoks)
toTokList t = pure [Expr t]

record BangData where
  constructor MkBangData
  nextName : Int
  bangNames : List (Name, FC, RawImp)

initBangs : BangData
initBangs = MkBangData 0 []

addNS : Maybe Namespace -> Name -> Name
addNS (Just ns) n@(NS _ _) = n
addNS (Just ns) n = NS ns n
addNS _ n = n

bindFun : FC -> Maybe Namespace -> RawImp -> RawImp -> RawImp
bindFun fc ns ma f =
  let fc = virtualiseFC fc in
  IApp fc (IApp fc (IVar fc (addNS ns $ UN ">>=")) ma) f

seqFun : FC -> Maybe Namespace -> RawImp -> RawImp -> RawImp
seqFun fc ns ma mb =
  let fc = virtualiseFC fc in
  IApp fc (IApp fc (IVar fc (addNS ns (UN ">>"))) ma) mb

bindBangs : List (Name, FC, RawImp) -> RawImp -> RawImp
bindBangs [] tm = tm
bindBangs ((n, fc, btm) :: bs) tm
    = bindBangs bs
    $ bindFun fc Nothing btm
    $ ILam EmptyFC top Explicit (Just n) (Implicit fc False) tm

idiomise : FC -> RawImp -> RawImp
idiomise fc (IAlternative afc u alts)
  = IAlternative afc (mapAltType (idiomise afc) u) (idiomise afc <$> alts)
idiomise fc (IApp afc f a)
    = let fc = virtualiseFC fc in
      IApp fc (IApp fc (IVar fc (UN "<*>"))
                       (idiomise afc f))
              a
idiomise fc fn
  = let fc = virtualiseFC fc in
    IApp fc (IVar fc (UN "pure")) fn

pairname : Name
pairname = NS builtinNS (UN "Pair")

mkpairname : Name
mkpairname = NS builtinNS (UN "MkPair")

dpairname : Name
dpairname = NS dpairNS (UN "DPair")

mkdpairname : Name
mkdpairname = NS dpairNS (UN "MkDPair")

data Bang : Type where

mutual
  desugarB : {auto s : Ref Syn SyntaxInfo} ->
             {auto b : Ref Bang BangData} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             Side -> List Name -> PTerm -> Core RawImp
  desugarB side ps (PRef fc x) = pure $ IVar fc x
  desugarB side ps (PPi fc rig p mn argTy retTy)
      = let ps' = maybe ps (:: ps) mn in
            pure $ IPi fc rig !(traverse (desugar side ps') p)
                              mn !(desugarB side ps argTy)
                                 !(desugarB side ps' retTy)
  desugarB side ps (PLam fc rig p pat@(PRef prefFC n@(UN nm)) argTy scope)
      =  if lowerFirst nm || nm == "_"
           then do whenJust (isConcreteFC prefFC) \nfc
                     => addSemanticDecorations [(nfc, Bound, Just n)]
                   pure $ ILam fc rig !(traverse (desugar AnyExpr ps) p)
                           (Just n) !(desugarB AnyExpr ps argTy)
                                    !(desugar AnyExpr (n :: ps) scope)
           else pure $ ILam EmptyFC rig !(traverse (desugar AnyExpr ps) p)
                   (Just (MN "lamc" 0)) !(desugarB AnyExpr ps argTy) $
                 ICase fc (IVar EmptyFC (MN "lamc" 0)) (Implicit fc False)
                     [snd !(desugarClause ps True (MkPatClause fc pat scope []))]
  desugarB side ps (PLam fc rig p (PRef _ n@(MN _ _)) argTy scope)
      = pure $ ILam fc rig !(traverse (desugar AnyExpr ps) p)
                           (Just n) !(desugarB AnyExpr ps argTy)
                                    !(desugar AnyExpr (n :: ps) scope)
  desugarB side ps (PLam fc rig p (PImplicit _) argTy scope)
      = pure $ ILam fc rig !(traverse (desugar AnyExpr ps) p)
                           Nothing !(desugarB AnyExpr ps argTy)
                                   !(desugar AnyExpr ps scope)
  desugarB side ps (PLam fc rig p pat argTy scope)
      = pure $ ILam EmptyFC rig !(traverse (desugar AnyExpr ps) p)
                   (Just (MN "lamc" 0)) !(desugarB AnyExpr ps argTy) $
                 ICase fc (IVar EmptyFC (MN "lamc" 0)) (Implicit fc False)
                     [snd !(desugarClause ps True (MkPatClause fc pat scope []))]
  desugarB side ps (PLet fc rig (PRef prefFC n) nTy nVal scope [])
      = do whenJust (isConcreteFC prefFC) \nfc =>
             addSemanticDecorations [(nfc, Bound, Just n)]
           pure $ ILet fc prefFC rig n !(desugarB side ps nTy) !(desugarB side ps nVal)
                                       !(desugar side (n :: ps) scope)
  desugarB side ps (PLet fc rig pat nTy nVal scope alts)
      = pure $ ICase fc !(desugarB side ps nVal) !(desugarB side ps nTy)
                        !(traverse (map snd . desugarClause ps True)
                            (MkPatClause fc pat scope [] :: alts))
  desugarB side ps (PCase fc x xs)
      = pure $ ICase fc !(desugarB side ps x)
                        (Implicit (virtualiseFC fc) False)
                        !(traverse (map snd . desugarClause ps True) xs)
  desugarB side ps (PLocal fc xs scope)
      = let ps' = definedIn xs ++ ps in
            pure $ ILocal fc (concat !(traverse (desugarDecl ps') xs))
                             !(desugar side ps' scope)
  desugarB side ps (PApp pfc (PUpdate fc fs) rec)
      = pure $ IUpdate pfc !(traverse (desugarUpdate side ps) fs)
                           !(desugarB side ps rec)
  desugarB side ps (PUpdate fc fs)
      = desugarB side ps
      $ let vfc = virtualiseFC fc in
      PLam vfc top Explicit (PRef vfc (MN "rec" 0)) (PImplicit vfc)
      $ PApp vfc (PUpdate fc fs) (PRef vfc (MN "rec" 0))
  desugarB side ps (PApp fc x y)
      = pure $ IApp fc !(desugarB side ps x) !(desugarB side ps y)
  desugarB side ps (PAutoApp fc x y)
      = pure $ IAutoApp fc !(desugarB side ps x) !(desugarB side ps y)
  desugarB side ps (PWithApp fc x y)
      = pure $ IWithApp fc !(desugarB side ps x) !(desugarB side ps y)
  desugarB side ps (PNamedApp fc x argn y)
      = pure $ INamedApp fc !(desugarB side ps x) argn !(desugarB side ps y)
  desugarB side ps (PDelayed fc r ty)
      = pure $ IDelayed fc r !(desugarB side ps ty)
  desugarB side ps (PDelay fc tm)
      = pure $ IDelay fc !(desugarB side ps tm)
  desugarB side ps (PForce fc tm)
      = pure $ IForce fc !(desugarB side ps tm)
  desugarB side ps (PEq fc l r)
      = do l' <- desugarB side ps l
           r' <- desugarB side ps r
           pure $ IAlternative fc FirstSuccess
                     [apply (IVar fc (UN "===")) [l', r'],
                      apply (IVar fc (UN "~=~")) [l', r']]
  desugarB side ps (PBracketed fc e) = desugarB side ps e
  desugarB side ps (POp fc opFC op l r)
      = do ts <- toTokList (POp fc opFC op l r)
           desugarTree side ps !(parseOps ts)
  desugarB side ps (PPrefixOp fc opFC op arg)
      = do ts <- toTokList (PPrefixOp fc opFC op arg)
           desugarTree side ps !(parseOps ts)
  desugarB side ps (PSectionL fc opFC op arg)
      = do syn <- get Syn
           -- It might actually be a prefix argument rather than a section
           -- so check that first, otherwise desugar as a lambda
           case lookup (nameRoot op) (prefixes syn) of
                Nothing =>
                   desugarB side ps (PLam fc top Explicit (PRef fc (MN "arg" 0)) (PImplicit fc)
                               (POp fc opFC op (PRef fc (MN "arg" 0)) arg))
                Just prec => desugarB side ps (PPrefixOp fc opFC op arg)
  desugarB side ps (PSectionR fc opFC arg op)
      = desugarB side ps (PLam fc top Explicit (PRef fc (MN "arg" 0)) (PImplicit fc)
                 (POp fc opFC op arg (PRef fc (MN "arg" 0))))
  desugarB side ps (PSearch fc depth) = pure $ ISearch fc depth
  desugarB side ps (PPrimVal fc (BI x))
      = case !fromIntegerName of
             Nothing =>
                pure $ IAlternative fc (UniqueDefault (IPrimVal fc (BI x)))
                                [IPrimVal fc (BI x),
                                 IPrimVal fc (I (fromInteger x))]
             Just fi =>
               let vfc = virtualiseFC fc in
               pure $ IApp vfc (IVar vfc fi) (IPrimVal fc (BI x))
  desugarB side ps (PPrimVal fc (Ch x))
      = case !fromCharName of
             Nothing =>
                pure $ IPrimVal fc (Ch x)
             Just f =>
               let vfc = virtualiseFC fc in
               pure $ IApp vfc (IVar vfc f) (IPrimVal fc (Ch x))
  desugarB side ps (PPrimVal fc (Db x))
      = case !fromDoubleName of
             Nothing =>
                pure $ IPrimVal fc (Db x)
             Just f =>
               let vfc = virtualiseFC fc in
               pure $ IApp vfc (IVar vfc f) (IPrimVal fc (Db x))
  desugarB side ps (PPrimVal fc x) = pure $ IPrimVal fc x
  desugarB side ps (PQuote fc tm)
      = pure $ IQuote fc !(desugarB side ps tm)
  desugarB side ps (PQuoteName fc n)
      = pure $ IQuoteName fc n
  desugarB side ps (PQuoteDecl fc x)
      = do xs <- traverse (desugarDecl ps) x
           pure $ IQuoteDecl fc (concat xs)
  desugarB side ps (PUnquote fc tm)
      = pure $ IUnquote fc !(desugarB side ps tm)
  desugarB side ps (PRunElab fc tm)
      = pure $ IRunElab fc !(desugarB side ps tm)
  desugarB side ps (PHole fc br holename)
      = do when br $
              do syn <- get Syn
                 put Syn (record { bracketholes $= ((UN holename) ::) } syn)
           pure $ IHole fc holename
  desugarB side ps (PType fc) = pure $ IType fc
  desugarB side ps (PAs fc nameFC vname pattern)
      = pure $ IAs fc nameFC UseRight vname !(desugarB side ps pattern)
  desugarB side ps (PDotted fc x)
      = pure $ IMustUnify fc UserDotted !(desugarB side ps x)
  desugarB side ps (PImplicit fc) = pure $ Implicit fc True
  desugarB side ps (PInfer fc)
    = do when (side == LHS) $
           throw (GenericMsg fc "? is not a valid pattern")
         pure $ Implicit fc False
  desugarB side ps (PMultiline fc indent lines)
      = addFromString fc !(expandString side ps fc !(trimMultiline fc indent lines))
  desugarB side ps (PString fc strs)
      = addFromString fc !(expandString side ps fc strs)
  desugarB side ps (PDoBlock fc ns block)
      = expandDo side ps fc ns block
  desugarB side ps (PBang fc term)
      = do itm <- desugarB side ps term
           bs <- get Bang
           let bn = MN "bind" (nextName bs)
           put Bang (record { nextName $= (+1),
                              bangNames $= ((bn, fc, itm) ::)
                            } bs)
           pure (IVar EmptyFC bn)
  desugarB side ps (PIdiom fc term)
      = do itm <- desugarB side ps term
           logRaw "desugar.idiom" 10 "Desugaring idiom for" itm
           let val = idiomise fc itm
           logRaw "desugar.idiom" 10 "Desugared to" val
           pure val
  desugarB side ps (PList fc nilFC args)
      = expandList side ps nilFC args
  desugarB side ps (PSnocList fc nilFC args)
      = expandSnocList side ps nilFC (reverse args)
  desugarB side ps (PPair fc l r)
      = do l' <- desugarB side ps l
           r' <- desugarB side ps r
           let pval = apply (IVar fc mkpairname) [l', r']
           pure $ IAlternative fc (UniqueDefault pval)
                  [apply (IVar fc pairname) [l', r'], pval]
  desugarB side ps (PDPair fc opFC (PRef nameFC n@(UN _)) (PImplicit _) r)
      = do r' <- desugarB side ps r
           let pval = apply (IVar opFC mkdpairname) [IVar nameFC n, r']
           let vfc = virtualiseFC nameFC
           whenJust (isConcreteFC nameFC) \nfc =>
             addSemanticDefault (nfc, Bound, Just n)
           pure $ IAlternative fc (UniqueDefault pval)
                  [apply (IVar opFC dpairname)
                      [Implicit vfc False,
                       ILam nameFC top Explicit (Just n) (Implicit vfc False) r'],
                   pval]
  desugarB side ps (PDPair fc opFC (PRef namefc n@(UN _)) ty r)
      = do ty' <- desugarB side ps ty
           r' <- desugarB side ps r
           pure $ apply (IVar opFC dpairname)
                        [ty', ILam namefc top Explicit (Just n) ty' r']
  desugarB side ps (PDPair fc opFC l (PImplicit _) r)
      = do l' <- desugarB side ps l
           r' <- desugarB side ps r
           pure $ apply (IVar opFC mkdpairname) [l', r']
  desugarB side ps (PDPair fc opFC l ty r)
      = throw (GenericMsg fc "Invalid dependent pair type")
  desugarB side ps (PUnit fc)
      = pure $ IAlternative fc (UniqueDefault (IVar fc (UN "MkUnit")))
               [IVar fc (UN "Unit"),
                IVar fc (UN "MkUnit")]
  desugarB side ps (PIfThenElse fc x t e)
      = let fc = virtualiseFC fc in
        pure $ ICase fc !(desugarB side ps x) (IVar fc (UN "Bool"))
                   [PatClause fc (IVar fc (UN "True")) !(desugar side ps t),
                    PatClause fc (IVar fc (UN "False")) !(desugar side ps e)]
  desugarB side ps (PComprehension fc ret conds)
      = desugarB side ps (PDoBlock fc Nothing (map guard conds ++ [toPure ret]))
    where
      guard : PDo -> PDo
      guard (DoExp fc tm) = DoExp fc (PApp fc (PRef fc (UN "guard")) tm)
      guard d = d

      toPure : PTerm -> PDo
      toPure tm = DoExp fc (PApp fc (PRef fc (UN "pure")) tm)
  desugarB side ps (PRewrite fc rule tm)
      = pure $ IRewrite fc !(desugarB side ps rule) !(desugarB side ps tm)
  desugarB side ps (PRange fc start next end)
      = let fc = virtualiseFC fc in
        desugarB side ps $ case next of
           Nothing => papply fc (PRef fc (UN "rangeFromTo")) [start,end]
           Just n  => papply fc (PRef fc (UN "rangeFromThenTo")) [start, n, end]
  desugarB side ps (PRangeStream fc start next)
      = let fc = virtualiseFC fc in
        desugarB side ps $ case next of
           Nothing => papply fc (PRef fc (UN "rangeFrom")) [start]
           Just n  => papply fc (PRef fc (UN "rangeFromThen")) [start, n]
  desugarB side ps (PUnifyLog fc lvl tm)
      = pure $ IUnifyLog fc lvl !(desugarB side ps tm)
  desugarB side ps (PPostfixApp fc rec projs)
      = desugarB side ps
      $ foldl (\x, (fc, proj) => PApp fc (PRef fc proj) x) rec projs
  desugarB side ps (PPostfixAppPartial fc projs)
      = do let vfc = virtualiseFC fc
           let var = PRef vfc (MN "paRoot" 0)
           desugarB side ps $
             PLam fc top Explicit var (PImplicit vfc) $
               foldl (\r, (fc, proj) => PApp fc (PRef fc proj) r) var projs
  desugarB side ps (PWithUnambigNames fc ns rhs)
      = IWithUnambigNames fc ns <$> desugarB side ps rhs

  desugarUpdate : {auto s : Ref Syn SyntaxInfo} ->
                  {auto b : Ref Bang BangData} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {auto m : Ref MD Metadata} ->
                  Side -> List Name -> PFieldUpdate -> Core IFieldUpdate
  desugarUpdate side ps (PSetField p v)
      = pure (ISetField p !(desugarB side ps v))
  desugarUpdate side ps (PSetFieldApp p v)
      = pure (ISetFieldApp p !(desugarB side ps v))

  expandList : {auto s : Ref Syn SyntaxInfo} ->
               {auto b : Ref Bang BangData} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto m : Ref MD Metadata} ->
               Side -> List Name ->
               (nilFC : FC) -> List (FC, PTerm) -> Core RawImp
  expandList side ps nilFC [] = pure (IVar nilFC (UN "Nil"))
  expandList side ps nilFC ((consFC, x) :: xs)
      = pure $ apply (IVar consFC (UN "::"))
                [!(desugarB side ps x), !(expandList side ps nilFC xs)]

  expandSnocList
             : {auto s : Ref Syn SyntaxInfo} ->
               {auto b : Ref Bang BangData} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto m : Ref MD Metadata} ->
               Side -> List Name -> (nilFC : FC) -> List (FC, PTerm) -> Core RawImp
  expandSnocList side ps nilFC [] = pure (IVar nilFC (UN "Lin"))
  expandSnocList side ps nilFC ((consFC, x) :: xs)
      = pure $ apply (IVar consFC (UN ":<"))
                [!(expandSnocList side ps nilFC xs) , !(desugarB side ps x)]

  addFromString : {auto c : Ref Ctxt Defs} ->
                  FC -> RawImp -> Core RawImp
  addFromString fc tm
      = pure $ case !fromStringName of
                    Nothing => tm
                    Just f =>
                      let fc = virtualiseFC fc in
                      IApp fc (IVar fc f) tm

  expandString : {auto s : Ref Syn SyntaxInfo} ->
                 {auto b : Ref Bang BangData} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 Side -> List Name -> FC -> List PStr -> Core RawImp
  expandString side ps fc xs
    = do xs <- traverse toRawImp (filter notEmpty $ mergeStrLit xs)
         pure $ case xs of
           [] => IPrimVal fc (Str "")
           (_ :: _) => foldr1 concatStr xs
    where
      toRawImp : PStr -> Core RawImp
      toRawImp (StrLiteral fc str) = pure $ IPrimVal fc (Str str)
      toRawImp (StrInterp fc tm) = desugarB side ps tm

      -- merge neighbouring StrLiteral
      mergeStrLit : List PStr -> List PStr
      mergeStrLit xs
          = case List.spanBy (\case StrLiteral fc str => Just (fc, str); _ => Nothing) xs of
                 ([], []) => []
                 ([], x::xs) => x :: mergeStrLit xs
                 (lits@(_::_), xs) => (StrLiteral (fst $ head lits) (fastConcat $ snd <$> lits)) :: mergeStrLit xs

      notEmpty : PStr -> Bool
      notEmpty (StrLiteral _ str) = str /= ""
      notEmpty (StrInterp _ _) = True

      concatStr : RawImp -> RawImp -> RawImp
      concatStr a b =
        let aFC = virtualiseFC (getFC a)
            bFC = virtualiseFC (getFC b)
        in IApp aFC (IApp bFC (IVar bFC (UN "++")) a) b

  trimMultiline : FC -> Nat -> List (List PStr) -> Core (List PStr)
  trimMultiline fc indent lines
      = if indent == 0
           then pure $ dropLastNL $ concat lines
           else do
             lines <- trimLast fc lines
             lines <- traverse (trimLeft indent) lines
             pure $ dropLastNL $ concat lines
    where
      trimLast : FC -> List (List PStr) -> Core (List (List PStr))
      trimLast fc lines with (snocList lines)
        trimLast fc [] | Empty = throw $ BadMultiline fc "Expected line wrap"
        trimLast _ (initLines `snoc` []) | Snoc [] initLines _ = pure lines
        trimLast _ (initLines `snoc` [StrLiteral fc str]) | Snoc [(StrLiteral _ _)] initLines _
            = if any (not . isSpace) (fastUnpack str)
                     then throw $ BadMultiline fc "Closing delimiter of multiline strings cannot be preceded by non-whitespace characters"
                     else pure initLines
        trimLast _ (initLines `snoc` xs) | Snoc xs initLines _
            = let fc = fromMaybe fc $ findBy isStrInterp xs in
                  throw $ BadMultiline fc "Closing delimiter of multiline strings cannot be preceded by non-whitespace characters"

      dropLastNL : List PStr -> List PStr
      dropLastNL pstrs with (snocList pstrs)
        dropLastNL [] | Empty = []
        dropLastNL (initLines `snoc` (StrLiteral fc str)) | Snoc (StrLiteral _ _) initLines _
            = initLines `snoc` (StrLiteral fc (fst $ break isNL str))
        dropLastNL pstrs | _ = pstrs

      trimLeft : Nat -> List PStr -> Core (List PStr)
      trimLeft indent [] = pure []
      trimLeft indent [(StrLiteral fc str)]
          = let (trimed, rest) = splitAt indent (fastUnpack str) in
                if any (not . isSpace) trimed
                   then throw $ BadMultiline fc "Line is less indented than the closing delimiter"
                   else pure $ [StrLiteral fc (fastPack rest)]
      trimLeft indent ((StrLiteral fc str)::xs)
          = let (trimed, rest) = splitAt indent (fastUnpack str) in
                if any (not . isSpace) trimed || length trimed < indent
                   then throw $ BadMultiline fc "Line is less indented than the closing delimiter"
                   else pure $ (StrLiteral fc (fastPack rest))::xs
      trimLeft indent xs = throw $ BadMultiline fc "Line is less indented than the closing delimiter"

  expandDo : {auto s : Ref Syn SyntaxInfo} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto m : Ref MD Metadata} ->
             Side -> List Name -> FC -> Maybe Namespace -> List PDo -> Core RawImp
  expandDo side ps fc ns [] = throw (GenericMsg fc "Do block cannot be empty")
  expandDo side ps _ _ [DoExp fc tm] = desugar side ps tm
  expandDo side ps fc ns [e]
      = throw (GenericMsg (getLoc e)
                  "Last statement in do block must be an expression")
  expandDo side ps topfc ns (DoExp fc tm :: rest)
      = do tm' <- desugar side ps tm
           rest' <- expandDo side ps topfc ns rest
           gam <- get Ctxt
           pure $ seqFun fc ns tm' rest'
  expandDo side ps topfc ns (DoBind fc nameFC n tm :: rest)
      = do tm' <- desugar side ps tm
           rest' <- expandDo side ps topfc ns rest
           whenJust (isConcreteFC nameFC) \nfc => addSemanticDecorations [(nfc, Bound, Just n)]
           pure $ bindFun fc ns tm'
                $ ILam nameFC top Explicit (Just n)
                       (Implicit (virtualiseFC fc) False) rest'
  expandDo side ps topfc ns (DoBindPat fc pat exp alts :: rest)
      = do pat' <- desugar LHS ps pat
           (newps, bpat) <- bindNames False pat'
           exp' <- desugar side ps exp
           alts' <- traverse (map snd . desugarClause ps True) alts
           let ps' = newps ++ ps
           rest' <- expandDo side ps' topfc ns rest
           let fcOriginal = fc
           let fc = virtualiseFC fc
           pure $ bindFun fc ns exp'
                $ ILam EmptyFC top Explicit (Just (MN "_" 0))
                          (Implicit fc False)
                          (ICase fc (IVar EmptyFC (MN "_" 0))
                               (Implicit fc False)
                               (PatClause fcOriginal bpat rest'
                                  :: alts'))
  expandDo side ps topfc ns (DoLet fc lhsFC n rig ty tm :: rest)
      = do b <- newRef Bang initBangs
           tm' <- desugarB side ps tm
           ty' <- desugar side ps ty
           rest' <- expandDo side ps topfc ns rest
           whenJust (isConcreteFC lhsFC) \nfc => addSemanticDecorations [(nfc, Bound, Just n)]
           let bind = ILet fc (virtualiseFC lhsFC) rig n ty' tm' rest'
           bd <- get Bang
           pure $ bindBangs (bangNames bd) bind
  expandDo side ps topfc ns (DoLetPat fc pat ty tm alts :: rest)
      = do b <- newRef Bang initBangs
           pat' <- desugar LHS ps pat
           ty' <- desugar side ps ty
           (newps, bpat) <- bindNames False pat'
           tm' <- desugarB side ps tm
           alts' <- traverse (map snd . desugarClause ps True) alts
           let ps' = newps ++ ps
           rest' <- expandDo side ps' topfc ns rest
           bd <- get Bang
           let fc = virtualiseFC fc
           pure $ bindBangs (bangNames bd) $
                    ICase fc tm' ty'
                       (PatClause fc bpat rest'
                                  :: alts')
  expandDo side ps topfc ns (DoLetLocal fc decls :: rest)
      = do rest' <- expandDo side ps topfc ns rest
           decls' <- traverse (desugarDecl ps) decls
           pure $ ILocal fc (concat decls') rest'
  expandDo side ps topfc ns (DoRewrite fc rule :: rest)
      = do rest' <- expandDo side ps topfc ns rest
           rule' <- desugar side ps rule
           pure $ IRewrite fc rule' rest'

  desugarTree : {auto s : Ref Syn SyntaxInfo} ->
                {auto b : Ref Bang BangData} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                Side -> List Name -> Tree OpStr PTerm -> Core RawImp
  desugarTree side ps (Infix loc eqFC (UN "=") l r) -- special case since '=' is special syntax
      = do l' <- desugarTree side ps l
           r' <- desugarTree side ps r
           pure (IAlternative loc FirstSuccess
                     [apply (IVar eqFC (UN "===")) [l', r'],
                      apply (IVar eqFC (UN "~=~")) [l', r']])
  desugarTree side ps (Infix loc _ (UN "$") l r) -- special case since '$' is special syntax
      = do l' <- desugarTree side ps l
           r' <- desugarTree side ps r
           pure (IApp loc l' r')
  desugarTree side ps (Infix loc opFC op l r)
      = do l' <- desugarTree side ps l
           r' <- desugarTree side ps r
           pure (IApp loc (IApp loc (IVar opFC op) l') r')

  -- negation is a special case, since we can't have an operator with
  -- two meanings otherwise
  --
  -- Note: In case of negated signed integer literals, we apply the
  -- negation directly. Otherwise, the literal might be
  -- truncated to 0 before being passed on to `negate`.
  desugarTree side ps (Pre loc opFC (UN "-") $ Leaf $ PPrimVal fc c)
    = let newFC    = fromMaybe EmptyFC (mergeFC loc fc)
          continue = desugarTree side ps . Leaf . PPrimVal newFC
       in case c of
            I   x => continue $ I (-x)
            I8  x => continue $ I8 (-x)
            I16 x => continue $ I16 (-x)
            I32 x => continue $ I32 (-x)
            I64 x => continue $ I64 (-x)
            BI  x => continue $ BI (-x)

            -- not a signed integer literal. proceed by desugaring
            -- and applying to `negate`.
            _     => do arg' <- desugarTree side ps (Leaf $ PPrimVal fc c)
                        pure (IApp loc (IVar opFC (UN "negate")) arg')

  desugarTree side ps (Pre loc opFC (UN "-") arg)
    = do arg' <- desugarTree side ps arg
         pure (IApp loc (IVar opFC (UN "negate")) arg')

  desugarTree side ps (Pre loc opFC op arg)
      = do arg' <- desugarTree side ps arg
           pure (IApp loc (IVar opFC op) arg')
  desugarTree side ps (Leaf t) = desugarB side ps t

  desugarType : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                List Name -> PTypeDecl -> Core ImpTy
  desugarType ps (MkPTy fc nameFC n d ty)
      = do addDocString n d
           syn <- get Syn
           pure $ MkImpTy fc nameFC n !(bindTypeNames fc (usingImpl syn)
                                               ps !(desugar AnyExpr ps ty))

  getClauseFn : RawImp -> Core Name
  getClauseFn (IVar _ n) = pure n
  getClauseFn (IApp _ f _) = getClauseFn f
  getClauseFn (IAutoApp _ f _) = getClauseFn f
  getClauseFn (INamedApp _ f _ _) = getClauseFn f
  getClauseFn tm = throw $ case tm of
    Implicit fc _ => GenericMsg fc "Invalid name for a declaration"
    _ => InternalError (show tm ++ " is not a function application")

  desugarLHS : {auto s : Ref Syn SyntaxInfo} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               List Name -> (arg : Bool) -> PTerm ->
               Core (IMaybe (not arg) Name, List Name, RawImp)
                  -- ^ we only look for the head name of the expression...
                  --   if we are actually looking at a headed thing!
  desugarLHS ps arg lhs =
    do rawlhs <- desugar LHS ps lhs
       inm <- iunless arg $ getClauseFn rawlhs
       (bound, blhs) <- bindNames arg rawlhs
       iwhenJust inm $ \ nm =>
         when (nm `elem` bound) $ do
           let fc = getPTermLoc lhs
           throw $ GenericMsg fc $ concat $ the (List String)
             [ "Declaration name ("
             , show nm
             , ") shadowed by a pattern variable."
             ]

       pure (inm, bound, blhs)

  desugarClause : {auto s : Ref Syn SyntaxInfo} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {auto m : Ref MD Metadata} ->
                  List Name -> (arg : Bool) -> PClause ->
                  Core (IMaybe (not arg) Name, ImpClause)
  desugarClause ps arg (MkPatClause fc lhs rhs wheres)
      = do ws <- traverse (desugarDecl ps) wheres

           (nm, bound, lhs') <- desugarLHS ps arg lhs

           -- desugar rhs, putting where clauses as local definitions
           rhs' <- desugar AnyExpr (bound ++ ps) rhs
           let rhs' = case ws of
                        [] => rhs'
                        _ => ILocal fc (concat ws) rhs'

           pure (nm, PatClause fc lhs' rhs')

  desugarClause ps arg (MkWithClause fc lhs wval prf flags cs)
      = do cs' <- traverse (map snd . desugarClause ps arg) cs
           (nm, bound, lhs') <- desugarLHS ps arg lhs
           wval' <- desugar AnyExpr (bound ++ ps) wval
           pure (nm, WithClause fc lhs' wval' prf flags cs')

  desugarClause ps arg (MkImpossible fc lhs)
      = do (nm, _, lhs') <- desugarLHS ps arg lhs
           pure (nm, ImpossibleClause fc lhs')

  desugarData : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                List Name -> (doc : String) ->
                PDataDecl -> Core ImpData
  desugarData ps doc (MkPData fc n tycon opts datacons)
      = do addDocString n doc
           syn <- get Syn
           pure $ MkImpData fc n
                              !(bindTypeNames fc (usingImpl syn)
                                              ps !(desugar AnyExpr ps tycon))
                              opts
                              !(traverse (desugarType ps) datacons)
  desugarData ps doc (MkPLater fc n tycon)
      = do addDocString n doc
           syn <- get Syn
           pure $ MkImpLater fc n !(bindTypeNames fc (usingImpl syn)
                                                  ps !(desugar AnyExpr ps tycon))

  desugarField : {auto s : Ref Syn SyntaxInfo} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 {auto m : Ref MD Metadata} ->
                 List Name -> Namespace -> PField ->
                 Core IField
  desugarField ps ns (MkField fc doc rig p n ty)
      = do addDocStringNS ns n doc
           addDocStringNS ns (toRF n) doc
           syn <- get Syn
           pure (MkIField fc rig !(traverse (desugar AnyExpr ps) p )
                          n !(bindTypeNames fc (usingImpl syn)
                          ps !(desugar AnyExpr ps ty)))
        where
          toRF : Name -> Name
          toRF (UN n) = RF n
          toRF n = n

  export
  desugarFnOpt : {auto s : Ref Syn SyntaxInfo} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 {auto m : Ref MD Metadata} ->
                 List Name -> PFnOpt -> Core FnOpt
  desugarFnOpt ps (IFnOpt f) = pure f
  desugarFnOpt ps (PForeign tms)
      = do tms' <- traverse (desugar AnyExpr ps) tms
           pure (ForeignFn tms')

  -- Given a high level declaration, return a list of TTImp declarations
  -- which process it, and update any necessary state on the way.
  export
  desugarDecl : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                List Name -> PDecl -> Core (List ImpDecl)
  desugarDecl ps (PClaim fc rig vis fnopts ty)
      = do opts <- traverse (desugarFnOpt ps) fnopts
           pure [IClaim fc rig vis opts !(desugarType ps ty)]
        where
          isTotalityOption : FnOpt -> Bool
          isTotalityOption (Totality _) = True
          isTotalityOption _            = False

  desugarDecl ps (PDef fc clauses)
  -- The clauses won't necessarily all be from the same function, so split
  -- after desugaring, by function name, using collectDefs from RawImp
      = do ncs <- traverse (desugarClause ps False) clauses
           defs <- traverse (uncurry $ toIDef . fromJust) ncs
           pure (collectDefs defs)
    where
      toIDef : Name -> ImpClause -> Core ImpDecl
      toIDef nm (PatClause fc lhs rhs)
          = pure $ IDef fc nm [PatClause fc lhs rhs]
      toIDef nm (WithClause fc lhs rhs prf flags cs)
          = pure $ IDef fc nm [WithClause fc lhs rhs prf flags cs]
      toIDef nm (ImpossibleClause fc lhs)
          = pure $ IDef fc nm [ImpossibleClause fc lhs]

  desugarDecl ps (PData fc doc vis ddecl)
      = pure [IData fc vis !(desugarData ps doc ddecl)]
  desugarDecl ps (PParameters fc params pds)
      = do pds' <- traverse (desugarDecl (ps ++ map fst params)) pds
           params' <- traverse (\(n, rig, i, ntm) => do tm' <- desugar AnyExpr ps ntm
                                                        i' <- traverse (desugar AnyExpr ps) i
                                                        pure (n, rig, i', tm')) params
           -- Look for implicitly bindable names in the parameters
           pnames <- ifThenElse (not !isUnboundImplicits) (pure [])
             $ map concat
             $ for (map (Builtin.snd . Builtin.snd . Builtin.snd) params')
             $ findUniqueBindableNames fc True (ps ++ map Builtin.fst params) []

           let paramsb = map (\(n, rig, info, tm) =>
                                 (n, rig, info, doBind pnames tm)) params'
           pure [IParameters fc paramsb (concat pds')]
  desugarDecl ps (PUsing fc uimpls uds)
      = do syn <- get Syn
           let oldu = usingImpl syn
           uimpls' <- traverse (\ ntm => do tm' <- desugar AnyExpr ps (snd ntm)
                                            btm <- bindTypeNames fc oldu ps tm'
                                            pure (fst ntm, btm)) uimpls
           put Syn (record { usingImpl = uimpls' ++ oldu } syn)
           uds' <- traverse (desugarDecl ps) uds
           syn <- get Syn
           put Syn (record { usingImpl = oldu } syn)
           pure (concat uds')
  desugarDecl ps (PReflect fc tm)
      = throw (GenericMsg fc "Reflection not implemented yet")
--       pure [IReflect fc !(desugar AnyExpr ps tm)]
  desugarDecl ps (PInterface fc vis cons_in tn doc params det conname body)
      = do addDocString tn doc
           let paramNames = map fst params

           let cons = concatMap expandConstraint cons_in
           cons' <- traverse (\ ntm => do tm' <- desugar AnyExpr (ps ++ paramNames)
                                                         (snd ntm)
                                          pure (fst ntm, tm')) cons
           params' <- traverse (\ (nm, (rig, tm)) =>
                         do tm' <- desugar AnyExpr ps tm
                            pure (nm, (rig, tm')))
                      params
           -- Look for bindable names in all the constraints and parameters
           let mnames = map dropNS (definedIn body)
           bnames <- ifThenElse (not !isUnboundImplicits) (pure [])
             $ map concat
             $ for (map Builtin.snd cons' ++ map (snd . snd) params')
             $ findUniqueBindableNames fc True (ps ++ mnames ++ paramNames) []

           let paramsb = map (\ (nm, (rig, tm)) =>
                                 let tm' = doBind bnames tm in
                                 (nm, (rig, tm')))
                         params'
           let consb = map (\ (nm, tm) => (nm, doBind bnames tm)) cons'

           body' <- traverse (desugarDecl (ps ++ mnames ++ paramNames)) body
           pure [IPragma (maybe [tn] (\n => [tn, n]) conname)
                         (\nest, env =>
                             elabInterface fc vis env nest consb
                                           tn paramsb det conname
                                           (concat body'))]
    where
      -- Turns pairs in the constraints to individual constraints. This
      -- is a bit of a hack, but it's necessary to build parent constraint
      -- chasing functions correctly
      pairToCons : PTerm -> List PTerm
      pairToCons (PPair _ l r) = pairToCons l ++ pairToCons r
      pairToCons t = [t]

      expandConstraint : (Maybe Name, PTerm) -> List (Maybe Name, PTerm)
      expandConstraint (Just n, t) = [(Just n, t)]
      expandConstraint (Nothing, p)
          = map (\x => (Nothing, x)) (pairToCons p)

  desugarDecl ps (PImplementation fc vis fnopts pass is cons tn params impln nusing body)
      = do opts <- traverse (desugarFnOpt ps) fnopts
           is' <- traverse (\ (n,c,tm) => do tm' <- desugar AnyExpr ps tm
                                             pure (n, c, tm')) is
           let _ = the (List (Name, RigCount, RawImp)) is'
           cons' <- traverse (\ (n, tm) => do tm' <- desugar AnyExpr ps tm
                                              pure (n, tm')) cons
           let _ = the (List (Maybe Name, RawImp)) cons'
           params' <- traverse (desugar AnyExpr ps) params
           let _ = the (List RawImp) params'
           -- Look for bindable names in all the constraints and parameters
           bnames <- ifThenElse (not !isUnboundImplicits) (pure [])
             $ map concat
             $ for (map snd cons' ++ params')
             $ findUniqueBindableNames fc True ps []

           let paramsb = map (doBind bnames) params'
           let isb = map (\ (n, r, tm) => (n, r, doBind bnames tm)) is'
           let _ = the (List (Name, RigCount, RawImp)) isb
           let consb = map (\(n, tm) => (n, doBind bnames tm)) cons'
           let _ = the (List (Maybe Name, RawImp)) consb

           body' <- maybe (pure Nothing)
                          (\b => do b' <- traverse (desugarDecl ps) b
                                    pure (Just (concat b'))) body
           -- calculate the name of the interface, if it's not explicitly
           -- given.
           let impname = maybe (mkImplName fc tn paramsb) id impln

           pure [IPragma [impname]
                         (\nest, env =>
                             elabImplementation fc vis opts pass env nest isb consb
                                                tn paramsb (isNamed impln)
                                                impname nusing
                                                body')]
    where
      isNamed : Maybe a -> Bool
      isNamed Nothing = False
      isNamed (Just _) = True

  desugarDecl ps (PRecord fc doc vis tn params conname_in fields)
      = do addDocString tn doc
           params' <- traverse (\ (n,c,p,tm) =>
                          do tm' <- desugar AnyExpr ps tm
                             p'  <- mapDesugarPiInfo ps p
                             pure (n, c, p', tm'))
                        params
           let _ = the (List (Name, RigCount, PiInfo RawImp, RawImp)) params'
           let fnames = map fname fields
           let _ = the (List Name) fnames
           -- Look for bindable names in the parameters

           let bnames = if !isUnboundImplicits
                        then concatMap (findBindableNames True
                                         (ps ++ fnames ++ map fst params) [])
                                       (map (\(_,_,_,d) => d) params')
                        else []
           let _ = the (List (String, String)) bnames

           let paramsb = map (\ (n, c, p, tm) => (n, c, p, doBind bnames tm)) params'
           let _ = the (List (Name, RigCount, PiInfo RawImp, RawImp)) paramsb
           let recName = nameRoot tn
           fields' <- traverse (desugarField (ps ++ map fname fields ++
                                              map fst params) (mkNamespace recName))
                               fields
           let _ = the (List IField) fields'
           let conname = maybe (mkConName tn) id conname_in
           let _ = the Name conname
           pure [IRecord fc (Just recName)
                         vis (MkImpRecord fc tn paramsb conname fields')]
    where
      fname : PField -> Name
      fname (MkField _ _ _ _ n _) = n

      mkConName : Name -> Name
      mkConName (NS ns (UN n)) = NS ns (DN n (MN ("__mk" ++ n) 0))
      mkConName n = DN (show n) (MN ("__mk" ++ show n) 0)

      mapDesugarPiInfo : List Name -> PiInfo PTerm -> Core (PiInfo RawImp)
      mapDesugarPiInfo ps = traverse (desugar AnyExpr ps)

  desugarDecl ps (PFixity fc Prefix prec (UN n))
      = do syn <- get Syn
           put Syn (record { prefixes $= insert n prec } syn)
           pure []
  desugarDecl ps (PFixity fc fix prec (UN n))
      = do syn <- get Syn
           put Syn (record { infixes $= insert n (fix, prec) } syn)
           pure []
  desugarDecl ps (PFixity fc _ _ _)
      = throw (GenericMsg fc "Fixity declarations must be for unqualified names")
  desugarDecl ps (PMutual fc ds)
      = do let (tys, defs) = splitMutual ds
           mds' <- traverse (desugarDecl ps) (tys ++ defs)
           pure (concat mds')
  desugarDecl ps (PNamespace fc ns decls)
      = withExtendedNS ns $ do
           ds <- traverse (desugarDecl ps) decls
           pure [INamespace fc ns (concat ds)]
  desugarDecl ps (PTransform fc n lhs rhs)
      = do (bound, blhs) <- bindNames False !(desugar LHS ps lhs)
           rhs' <- desugar AnyExpr (bound ++ ps) rhs
           pure [ITransform fc (UN n) blhs rhs']
  desugarDecl ps (PRunElabDecl fc tm)
      = do tm' <- desugar AnyExpr ps tm
           pure [IRunElabDecl fc tm']
  desugarDecl ps (PDirective fc d)
      = case d of
             Hide n => pure [IPragma [] (\nest, env => hide fc n)]
             Logging i => pure [ILog ((\ i => (topics i, verbosity i)) <$> i)]
             LazyOn a => pure [IPragma [] (\nest, env => lazyActive a)]
             UnboundImplicits a => do
               setUnboundImplicits a
               pure [IPragma [] (\nest, env => setUnboundImplicits a)]
             PrefixRecordProjections b => do
               pure [IPragma [] (\nest, env => setPrefixRecordProjections b)]
             AmbigDepth n => pure [IPragma [] (\nest, env => setAmbigLimit n)]
             AutoImplicitDepth n => pure [IPragma [] (\nest, env => setAutoImplicitLimit n)]
             NFMetavarThreshold n => pure [IPragma [] (\nest, env => setNFThreshold n)]
             SearchTimeout n => pure [IPragma [] (\nest, env => setSearchTimeout n)]
             PairNames ty f s => pure [IPragma [] (\nest, env => setPair fc ty f s)]
             RewriteName eq rw => pure [IPragma [] (\nest, env => setRewrite fc eq rw)]
             PrimInteger n => pure [IPragma [] (\nest, env => setFromInteger n)]
             PrimString n => pure [IPragma [] (\nest, env => setFromString n)]
             PrimChar n => pure [IPragma [] (\nest, env => setFromChar n)]
             PrimDouble n => pure [IPragma [] (\nest, env => setFromDouble n)]
             CGAction cg dir => pure [IPragma [] (\nest, env => addDirective cg dir)]
             Names n ns => pure [IPragma [] (\nest, env => addNameDirective fc n ns)]
             StartExpr tm => pure [IPragma [] (\nest, env => throw (InternalError "%start not implemented"))] -- TODO!
             Overloadable n => pure [IPragma [] (\nest, env => setNameFlag fc n Overloadable)]
             Extension e => pure [IPragma [] (\nest, env => setExtension e)]
             DefaultTotality tot => pure [IPragma [] (\_, _ => setDefaultTotalityOption tot)]
             PatternSynonym n => pure [IPragma [] (\nest, env => addImplicitPattern fc n)]
  desugarDecl ps (PBuiltin fc type name) = pure [IBuiltin fc type name]

  export
  desugar : {auto s : Ref Syn SyntaxInfo} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            Side -> List Name -> PTerm -> Core RawImp
  desugar s ps tm
      = do b <- newRef Bang initBangs
           tm' <- desugarB s ps tm
           bd <- get Bang
           pure $ bindBangs (bangNames bd) tm'
