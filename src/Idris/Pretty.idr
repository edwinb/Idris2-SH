module Idris.Pretty

import Data.List
import Data.Strings
import Control.ANSI.SGR
import public Text.PrettyPrint.Prettyprinter
import public Text.PrettyPrint.Prettyprinter.Render.Terminal
import public Text.PrettyPrint.Prettyprinter.Util

import Algebra
import Idris.REPLOpts
import Idris.Syntax
import Utils.Term

%default covering

public export
data IdrisAnn
  = Warning
  | Error
  | ErrorDesc
  | FileCtxt
  | Code
  | Meta
  | Keyword
  | Pragma

export
colorAnn : IdrisAnn -> AnsiStyle
colorAnn Warning = color Yellow <+> bold
colorAnn Error = color BrightRed <+> bold
colorAnn ErrorDesc = bold
colorAnn FileCtxt = color BrightBlue
colorAnn Code = color Magenta
colorAnn Keyword = color Red
colorAnn Pragma = color BrightMagenta
colorAnn Meta = color Green

export
error : Doc IdrisAnn -> Doc IdrisAnn
error = annotate Error

export
errorDesc : Doc IdrisAnn -> Doc IdrisAnn
errorDesc = annotate ErrorDesc

export
fileCtxt : Doc IdrisAnn -> Doc IdrisAnn
fileCtxt = annotate FileCtxt

export
keyword : Doc IdrisAnn -> Doc IdrisAnn
keyword = annotate Keyword

export
meta : Doc IdrisAnn -> Doc IdrisAnn
meta = annotate Meta

export
code : Doc IdrisAnn -> Doc IdrisAnn
code = annotate Code

let_ : Doc IdrisAnn
let_ = keyword (pretty "let")

in_ : Doc IdrisAnn
in_ = keyword (pretty "in")

case_ : Doc IdrisAnn
case_ = keyword (pretty "case")

of_ : Doc IdrisAnn
of_ = keyword (pretty "of")

do_ : Doc IdrisAnn
do_ = keyword (pretty "do")

with_ : Doc IdrisAnn
with_ = keyword (pretty "with")

record_ : Doc IdrisAnn
record_ = keyword (pretty "record")

impossible_ : Doc IdrisAnn
impossible_ = keyword (pretty "impossible")

auto_ : Doc IdrisAnn
auto_ = keyword (pretty "auto")

default_ : Doc IdrisAnn
default_ = keyword (pretty "default")

rewrite_ : Doc IdrisAnn
rewrite_ = keyword (pretty "rewrite")

export
pragma : Doc IdrisAnn -> Doc IdrisAnn
pragma = annotate Pragma

export
prettyRig : RigCount -> Doc ann
prettyRig = elimSemi (pretty '0' <+> space)
                     (pretty '1' <+> space)
                     (const emptyDoc)

mutual
  prettyAlt : PClause -> Doc IdrisAnn
  prettyAlt (MkPatClause _ lhs rhs _) =
    space <+> pipe <++> prettyTerm lhs <++> pretty "=>" <++> prettyTerm rhs <+> semi
  prettyAlt (MkWithClause _ lhs wval flags cs) =
    space <+> pipe <++> angles (angles (reflow "with alts not possible")) <+> semi
  prettyAlt (MkImpossible _ lhs) =
    space <+> pipe <++> prettyTerm lhs <++> impossible_ <+> semi

  prettyCase : PClause -> Doc IdrisAnn
  prettyCase (MkPatClause _ lhs rhs _) =
    prettyTerm lhs <++> pretty "=>" <++> prettyTerm rhs
  prettyCase (MkWithClause _ lhs rhs flags _) =
    space <+> pipe <++> angles (angles (reflow "with alts not possible"))
  prettyCase (MkImpossible _ lhs) =
    prettyTerm lhs <++> impossible_

  prettyDo : PDo -> Doc IdrisAnn
  prettyDo (DoExp _ tm) = prettyTerm tm
  prettyDo (DoBind _ n tm) = pretty n <++> pretty "<-" <++> prettyTerm tm
  prettyDo (DoBindPat _ l tm alts) =
    prettyTerm l <++> pretty "<-" <++> prettyTerm tm <+> hang 4 (fillSep $ prettyAlt <$> alts)
  prettyDo (DoLet _ l rig _ tm) =
    let_ <++> prettyRig rig <+> pretty l <++> equals <++> prettyTerm tm
  prettyDo (DoLetPat _ l _ tm alts) =
    let_ <++> prettyTerm l <++> equals <++> prettyTerm tm <+> hang 4 (fillSep $ prettyAlt <$> alts)
  prettyDo (DoLetLocal _ ds) =
    let_ <++> braces (angles (angles (pretty "definitions")))
  prettyDo (DoRewrite _ rule) = rewrite_ <+> prettyTerm rule

  prettyUpdate : PFieldUpdate -> Doc IdrisAnn
  prettyUpdate (PSetField path v) =
    concatWith (surround dot) (pretty <$> path) <++> equals <++> prettyTerm v
  prettyUpdate (PSetFieldApp path v) =
    concatWith (surround dot) (pretty <$> path) <++> pretty '$' <+> equals <++> prettyTerm v

  export
  prettyTerm : PTerm -> Doc IdrisAnn
  prettyTerm = go Open
    where
      startPrec : Prec
      startPrec = User 0
      appPrec : Prec
      appPrec = User 10
      leftAppPrec : Prec
      leftAppPrec = User 9

      go : Prec -> PTerm -> Doc IdrisAnn
      go d (PRef _ n) = pretty n
      go d (PPi _ rig Explicit Nothing arg ret) =
        parenthesise (d > startPrec) $ group $
          branchVal
            (go startPrec arg <++> "->" <++> go startPrec ret)
            (parens (prettyRig rig <+> "_" <++> colon <++> go startPrec arg) <++> "->" <+> line <+> go startPrec ret)
            rig
      go d (PPi _ rig Explicit (Just n) arg ret) =
        parenthesise (d > startPrec) $ group $
          parens (prettyRig rig <+> pretty n <++> colon <++> go startPrec arg) <++> "->" <+> line <+> go startPrec ret
      go d (PPi _ rig Implicit Nothing arg ret) =
        parenthesise (d > startPrec) $ group $
          braces (prettyRig rig <+> pretty '_' <++> colon <++> go startPrec arg) <++> "->" <+> line <+> go startPrec ret
      go d (PPi _ rig Implicit (Just n) arg ret) =
        parenthesise (d > startPrec) $ group $
          braces (prettyRig rig <+> pretty n <++> colon <++> go startPrec arg) <++> "->" <+> line <+> go startPrec ret
      go d (PPi _ rig AutoImplicit Nothing arg ret) =
        parenthesise (d > startPrec) $ group $
          branchVal
            (go startPrec arg <++> "=>" <+> line <+> go startPrec ret)
            (braces (auto_ <++> prettyRig rig <+> "_" <++> colon <++> go startPrec arg) <++> "->" <+> line <+> go startPrec ret)
            rig
      go d (PPi _ rig AutoImplicit (Just n) arg ret) =
        parenthesise (d > startPrec) $ group $
          braces (auto_ <++> prettyRig rig <+> pretty n <++> colon <++> go startPrec arg) <++> "->" <+> line <+> go startPrec ret
      go d (PPi _ rig (DefImplicit t) Nothing arg ret) =
        parenthesise (d > startPrec) $ group $
          braces (default_ <++> go appPrec t <++> prettyRig rig <+> "_" <++> colon <++> go startPrec arg) <++> "->" <+> line <+> go startPrec ret
      go d (PPi _ rig (DefImplicit t) (Just n) arg ret) =
        parenthesise (d > startPrec) $ group $
          braces (default_ <++> go appPrec t <++> prettyRig rig <+> pretty n <++> colon <++> go startPrec arg) <++> "->" <+> line <+> go startPrec ret
      go d (PLam _ rig p n ty sc) =
          let (ns, sc) = getLamNames [(rig, p, n, ty)] sc in
              parenthesise (d > startPrec) $ group $ align $ hang 2 $
                backslash <+> prettyBindings ns <++> "=>" <+> line <+> go startPrec sc
        where
          getLamNames : List (RigCount, PiInfo PTerm, PTerm, PTerm) -> PTerm -> (List (RigCount, PiInfo PTerm, PTerm, PTerm), PTerm)
          getLamNames acc (PLam _ rig p n ty sc) = getLamNames ((rig, p, n, ty) :: acc) sc
          getLamNames acc sc = (reverse acc, sc)
          prettyBindings : List (RigCount, PiInfo PTerm, PTerm, PTerm) -> Doc IdrisAnn
          prettyBindings [] = neutral
          prettyBindings [(rig, Implicit, n, (PImplicit _))] = "$" <+> braces (prettyRig rig <+> go startPrec n)
          prettyBindings [(rig, Implicit, n, ty)] = "$" <+> braces (prettyRig rig <+> go startPrec n <++> colon <++> go startPrec ty)
          prettyBindings [(rig, p, n, (PImplicit _))] = prettyRig rig <+> go startPrec n
          prettyBindings [(rig, p, n, ty)] = prettyRig rig <+> go startPrec n <++> colon <++> go startPrec ty
          prettyBindings ((rig, Implicit, n, (PImplicit _)) :: ns) = "$" <+> braces (prettyRig rig <+> go startPrec n) <+> comma <+> line <+> prettyBindings ns
          prettyBindings ((rig, Implicit, n, ty) :: ns) = "$" <+> braces (prettyRig rig <+> go startPrec n) <++> colon <++> go startPrec ty <+> comma <+> line <+> prettyBindings ns
          prettyBindings ((rig, p, n, (PImplicit _)) :: ns) = prettyRig rig <+> go startPrec n <+> comma <+> line <+> prettyBindings ns
          prettyBindings ((rig, p, n, ty) :: ns) = prettyRig rig <+> go startPrec n <++> colon <++> go startPrec ty <+> comma <+> line <+> prettyBindings ns
      go d (PLet _ rig n (PImplicit _) val sc alts) =
        parenthesise (d > startPrec) $ group $ align $
          let_ <++> (group $ align $ hang 2 $ prettyRig rig <+> go startPrec n <++> equals <+> line <+> go startPrec val) <+> line
            <+> in_ <++> (group $ align $ hang 2 $ go startPrec sc)
      go d (PLet _ rig n ty val sc alts) =
        parenthesise (d > startPrec) $ group $ align $
          let_ <++> (group $ align $ hang 2 $ prettyRig rig <+> go startPrec n <++> colon <++> go startPrec ty <++> equals <+> line <+> go startPrec val) <+> hardline
            <+> hang 4 (fillSep (prettyAlt <$> alts)) <+> line <+> in_ <++> (group $ align $ hang 2 $ go startPrec sc)
      go d (PCase _ tm cs) =
        parenthesise (d > appPrec) $ align $ case_ <++> go startPrec tm <++> of_ <+> line <+>
          braces (vsep $ punctuate semi (prettyCase <$> cs))
      go d (PLocal _ ds sc) =
        parenthesise (d > startPrec) $ group $ align $
          let_ <++> braces (angles (angles "definitions")) <+> line <+> in_ <++> go startPrec sc
      go d (PUpdate _ fs) =
        parenthesise (d > appPrec) $ group $ record_ <++> braces (vsep $ punctuate comma (prettyUpdate <$> fs))
      go d (PApp _ f a) = parenthesise (d > appPrec) $ group $ go leftAppPrec f <++> go appPrec a
      go d (PWithApp _ f a) = go d f <++> pipe <++> go d a
      go d (PDelayed _ LInf ty) = parenthesise (d > appPrec) $ "Inf" <++> go appPrec ty
      go d (PDelayed _ _ ty) = parenthesise (d > appPrec) $ "Lazy" <++> go appPrec ty
      go d (PDelay _ tm) = parenthesise (d > appPrec) $ "Delay" <++> go appPrec tm
      go d (PForce _ tm) = parenthesise (d > appPrec) $ "Force" <++> go appPrec tm
      go d (PAutoApp _ f a) =
        parenthesise (d > appPrec) $ group $ go leftAppPrec f <++> "@" <+> braces (go startPrec a)
      go d (PNamedApp _ f n (PRef _ a)) =
        parenthesise (d > appPrec) $ group $
          if n == a
             then go leftAppPrec f <++> braces (pretty n)
             else go leftAppPrec f <++> braces (pretty n <++> equals <++> pretty a)
      go d (PNamedApp _ f n a) =
        parenthesise (d > appPrec) $ group $ go leftAppPrec f <++> braces (pretty n <++> equals <++> go d a)
      go d (PSearch _ _) = pragma "%search"
      go d (PQuote _ tm) = parenthesise (d > appPrec) $ "`" <+> parens (go startPrec tm)
      go d (PQuoteName _ n) = parenthesise (d > appPrec) $ "`" <+> braces (braces (pretty n))
      go d (PQuoteDecl _ tm) = parenthesise (d > appPrec) $ "`" <+> brackets (angles (angles (pretty "declaration")))
      go d (PUnquote _ tm) = parenthesise (d > appPrec) $ "~" <+> parens (go startPrec tm)
      go d (PRunElab _ tm) = parenthesise (d > appPrec) $ pragma "%runElab" <++> go startPrec tm
      go d (PPrimVal _ c) = pretty c
      go d (PHole _ _ n) = meta (pretty (strCons '?' n))
      go d (PType _) = pretty "Type"
      go d (PAs _ n p) = pretty n <+> "@" <+> go d p
      go d (PDotted _ p) = dot <+> go d p
      go d (PImplicit _) = "_"
      go d (PInfer _) = "?"
      go d (POp _ op x y) = parenthesise (d > appPrec) $ group $ go startPrec x <++> pretty op <++> go startPrec y
      go d (PPrefixOp _ op x) = parenthesise (d > appPrec) $ pretty op <+> go startPrec x
      go d (PSectionL _ op x) = parens (pretty op <++> go startPrec x)
      go d (PSectionR _ x op) = parens (go startPrec x <++> pretty op)
      go d (PEq fc l r) = parenthesise (d > appPrec) $ go startPrec l <++> equals <++> go startPrec r
      go d (PBracketed _ tm) = parens (go startPrec tm)
      go d (PDoBlock _ ns ds) = parenthesise (d > appPrec) $ group $ align $ hang 2 $ do_ <++> (vsep $ punctuate semi (prettyDo <$> ds))
      go d (PBang _ tm) = "!" <+> go d tm
      go d (PIdiom _ tm) = enclose (pretty "[|") (pretty "|]") (go startPrec tm)
      go d (PList _ xs) = brackets (group $ align $ vsep $ punctuate comma (go startPrec <$> xs))
      go d (PPair _ l r) = group $ parens (go startPrec l <+> comma <+> line <+> go startPrec r)
      go d (PDPair _ l (PImplicit _) r) = group $ parens (go startPrec l <++> pretty "**" <+> line <+> go startPrec r)
      go d (PDPair _ l ty r) = group $ parens (go startPrec l <++> colon <++> go startPrec ty <++> pretty "**" <+> line <+> go startPrec r)
      go d (PUnit _) = "()"
      go d (PIfThenElse _ x t e) =
        parenthesise (d > appPrec) $ group $ align $ hang 2 $ vsep
          [keyword "if" <++> go startPrec x, keyword "then" <++> go startPrec t, keyword "else" <++> go startPrec e]
      go d (PComprehension _ ret es) =
          group $ brackets (go startPrec (dePure ret) <++> pipe <++> vsep (punctuate comma (prettyDo . deGuard <$> es)))
        where
          dePure : PTerm -> PTerm
          dePure tm@(PApp _ (PRef _ n) arg) = if dropNS n == UN "pure" then arg else tm
          dePure tm = tm

          deGuard : PDo -> PDo
          deGuard tm@(DoExp fc (PApp _ (PRef _ n) arg)) = if dropNS n == UN "guard" then DoExp fc arg else tm
          deGuard tm = tm
      go d (PRewrite _ rule tm) =
        parenthesise (d > appPrec) $ group $ rewrite_ <++> go startPrec rule <+> line <+> in_ <++> go startPrec tm
      go d (PRange _ start Nothing end) =
        brackets (go startPrec start <++> pretty ".." <++> go startPrec end)
      go d (PRange _ start (Just next) end) =
        brackets (go startPrec start <+> comma <++> go startPrec next <++> pretty ".." <++> go startPrec end)
      go d (PRangeStream _ start Nothing) = brackets (go startPrec start <++> pretty "..")
      go d (PRangeStream _ start (Just next)) =
        brackets (go startPrec start <+> comma <++> go startPrec next <++> pretty "..")
      go d (PUnifyLog _ lvl tm) = go d tm
      go d (PPostfixApp fc rec fields) =
        parenthesise (d > appPrec) $ go startPrec rec <++> dot <+> concatWith (surround dot) (map pretty fields)
      go d (PPostfixAppPartial fc fields) =
        parens (dot <+> concatWith (surround dot) (map pretty fields))
      go d (PWithUnambigNames fc ns rhs) = parenthesise (d > appPrec) $ group $ with_ <++> pretty ns <+> line <+> go startPrec rhs

getPageWidth : {auto o : Ref ROpts REPLOpts} -> Core PageWidth
getPageWidth = do
  consoleWidth <- getConsoleWidth
  case consoleWidth of
    Nothing => do
      cols <- coreLift getTermCols
      pure $ if cols == 0 then Unbounded else AvailablePerLine cols 1
    Just 0 => pure $ Unbounded
    Just cw => pure $ AvailablePerLine (cast cw) 1

export
render : {auto o : Ref ROpts REPLOpts} -> Doc IdrisAnn -> Core String
render doc = do
  color <- getColor
  pageWidth <- getPageWidth
  let opts = MkLayoutOptions pageWidth
  let layout = layoutPretty opts doc
  pure $ renderString $ if color then reAnnotateS colorAnn layout else unAnnotateS layout

export
renderWithoutColor : {auto o : Ref ROpts REPLOpts} -> Doc IdrisAnn -> Core String
renderWithoutColor doc = do
  pageWidth <- getPageWidth
  let opts = MkLayoutOptions pageWidth
  let layout = layoutPretty opts doc
  pure $ renderString $ unAnnotateS layout
