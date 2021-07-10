module Idris.Parser

import Core.Options
import Core.Metadata
import Idris.Syntax
import public Parser.Source
import Parser.Lexer.Source
import TTImp.TTImp

import public Libraries.Text.Parser
import Data.Either
import Data.List
import Data.List.Views
import Data.List1
import Data.Maybe
import Data.String
import Libraries.Utils.String

import Idris.Parser.Let

%default covering

decorate : OriginDesc -> Decoration -> Rule a -> Rule a
decorate fname decor rule = do
  res <- bounds rule
  act [((fname, (start res, end res)), decor, Nothing)]
  pure res.val


decorationFromBounded : OriginDesc -> Decoration -> WithBounds a -> ASemanticDecoration
decorationFromBounded fname decor bnds
   = ((fname, start bnds, end bnds), decor, Nothing)

boundedNameDecoration : OriginDesc -> Decoration -> WithBounds Name -> ASemanticDecoration
boundedNameDecoration fname decor bstr = ((fname, start bstr, end bstr)
                                         , decor
                                         , Just bstr.val)

decorateBoundedNames : OriginDesc -> Decoration -> List (WithBounds Name) -> EmptyRule ()
decorateBoundedNames fname decor bns = act $ map (boundedNameDecoration fname decor) bns

decorateBoundedName : OriginDesc -> Decoration -> WithBounds Name -> EmptyRule ()
decorateBoundedName fname decor bn = act [boundedNameDecoration fname decor bn]

decorateKeywords : OriginDesc -> List (WithBounds a) -> EmptyRule ()
decorateKeywords fname = act . map (decorationFromBounded fname Keyword)

dependentDecorate : OriginDesc -> Rule a -> (a -> Decoration) -> Rule a
dependentDecorate fname rule decor = do
  res <- bounds rule
  act [((fname, (start res, end res)), decor res.val, Nothing)]
  pure res.val

decoratedKeyword : OriginDesc -> String -> Rule ()
decoratedKeyword fname kwd = decorate fname Keyword (keyword kwd)

decoratedSymbol : OriginDesc -> String -> Rule ()
decoratedSymbol fname smb = decorate fname Keyword (symbol smb)

decoratedDataTypeName : OriginDesc -> Rule Name
decoratedDataTypeName fname = decorate fname Typ dataTypeName

decoratedDataConstructorName : OriginDesc -> Rule Name
decoratedDataConstructorName fname = decorate fname Data dataConstructorName

decoratedSimpleBinderName : OriginDesc -> Rule String
decoratedSimpleBinderName fname = decorate fname Bound unqualifiedName

-- Forward declare since they're used in the parser
topDecl : OriginDesc -> IndentInfo -> Rule (List PDecl)
collectDefs : List PDecl -> List PDecl

-- Some context for the parser
public export
record ParseOpts where
  constructor MkParseOpts
  eqOK : Bool -- = operator is parseable
  withOK : Bool -- = with applications are parseable

peq : ParseOpts -> ParseOpts
peq = record { eqOK = True }

pnoeq : ParseOpts -> ParseOpts
pnoeq = record { eqOK = False }

export
pdef : ParseOpts
pdef = MkParseOpts True True

pnowith : ParseOpts
pnowith = MkParseOpts True False

export
plhs : ParseOpts
plhs = MkParseOpts False False

%hide Prelude.(>>)
%hide Prelude.(>>=)
%hide Core.Core.(>>)
%hide Core.Core.(>>=)
%hide Prelude.pure
%hide Core.Core.pure
%hide Prelude.(<*>)
%hide Core.Core.(<*>)

atom : OriginDesc -> Rule PTerm
atom fname
    = do x <- bounds $ decorate fname Typ $ exactIdent "Type"
         pure (PType (boundToFC fname x))
  <|> do x <- bounds $ name
         pure (PRef (boundToFC fname x) x.val)
  <|> do x <- bounds $ dependentDecorate fname constant \c =>
                       if isPrimType c
                       then Typ
                       else Data
         pure (PPrimVal (boundToFC fname x) x.val)
  <|> do x <- bounds $ decoratedSymbol fname "_"
         pure (PImplicit (boundToFC fname x))
  <|> do x <- bounds $ symbol "?"
         pure (PInfer (boundToFC fname x))
  <|> do x <- bounds $ holeName
         pure (PHole (boundToFC fname x) False x.val)
  <|> do x <- bounds $ decorate fname Data $ pragma "MkWorld"
         pure (PPrimVal (boundToFC fname x) WorldVal)
  <|> do x <- bounds $ decorate fname Typ  $ pragma "World"
         pure (PPrimVal (boundToFC fname x) WorldType)
  <|> do x <- bounds $ pragma "search"
         pure (PSearch (boundToFC fname x) 50)

whereBlock : OriginDesc -> Int -> Rule (List PDecl)
whereBlock fname col
    = do decoratedKeyword fname "where"
         ds <- blockAfter col (topDecl fname)
         pure (collectDefs (concat ds))

-- Expect a keyword, but if we get anything else it's a fatal error
commitKeyword : OriginDesc -> IndentInfo -> String -> Rule ()
commitKeyword fname indents req
    = do mustContinue indents (Just req)
         decoratedKeyword fname req
         mustContinue indents Nothing

commitSymbol : String -> Rule ()
commitSymbol req
    = symbol req
       <|> fatalError ("Expected '" ++ req ++ "'")

continueWithDecorated : OriginDesc -> IndentInfo -> String -> Rule ()
continueWithDecorated fname indents req
    = mustContinue indents (Just req) *> decoratedSymbol fname req


continueWith : IndentInfo -> String -> Rule ()
continueWith indents req
    = mustContinue indents (Just req) *> symbol req

iOperator : Rule Name
iOperator
    = operator <|> (symbol "`" *> name <* symbol "`")

data ArgType
    = UnnamedExpArg PTerm
    | UnnamedAutoArg PTerm
    | NamedArg Name PTerm
    | WithArg PTerm

argTerm : ArgType -> PTerm
argTerm (UnnamedExpArg t) = t
argTerm (UnnamedAutoArg t) = t
argTerm (NamedArg _ t) = t
argTerm (WithArg t) = t

mutual
  appExpr : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  appExpr q fname indents
      = case_ fname indents
    <|> doBlock fname indents
    <|> lam fname indents
    <|> lazy fname indents
    <|> if_ fname indents
    <|> with_ fname indents
    <|> do b <- bounds (MkPair <$> simpleExpr fname indents <*> many (argExpr q fname indents))
           (f, args) <- pure b.val
           pure (applyExpImp (start b) (end b) f (concat args))
    <|> do b <- bounds (MkPair <$> bounds iOperator <*> expr pdef fname indents)
           (op, arg) <- pure b.val
           pure (PPrefixOp (boundToFC fname b) (boundToFC fname op) op.val arg)
    <|> fail "Expected 'case', 'if', 'do', application or operator expression"
    where
      applyExpImp : FilePos -> FilePos -> PTerm ->
                    List ArgType ->
                    PTerm
      applyExpImp start end f [] = f
      applyExpImp start end f (UnnamedExpArg exp :: args)
          = applyExpImp start end (PApp (MkFC fname start end) f exp) args
      applyExpImp start end f (UnnamedAutoArg imp :: args)
          = applyExpImp start end (PAutoApp (MkFC fname start end) f imp) args
      applyExpImp start end f (NamedArg n imp :: args)
          = let fc = MkFC fname start end in
            applyExpImp start end (PNamedApp fc f n imp) args
      applyExpImp start end f (WithArg exp :: args)
          = applyExpImp start end (PWithApp (MkFC fname start end) f exp) args

  argExpr : ParseOpts -> OriginDesc -> IndentInfo -> Rule (List ArgType)
  argExpr q fname indents
      = do continue indents
           arg <- simpleExpr fname indents
           the (EmptyRule _) $ case arg of
                PHole loc _ n => pure [UnnamedExpArg (PHole loc True n)]
                t => pure [UnnamedExpArg t]
    <|> do continue indents
           braceArgs fname indents
    <|> if withOK q
           then do continue indents
                   decoratedSymbol fname "|"
                   arg <- expr (record {withOK = False} q) fname indents
                   pure [WithArg arg]
           else fail "| not allowed here"
    where
      underscore : FC -> ArgType
      underscore fc = NamedArg (UN "_") (PImplicit fc)

      braceArgs : OriginDesc -> IndentInfo -> Rule (List ArgType)
      braceArgs fname indents
          = do start <- bounds (decoratedSymbol fname "{")
               list <- sepBy (decoratedSymbol fname ",")
                        $ do x <- bounds (decoratedSimpleBinderName fname)
                             let fc = boundToFC fname x
                             option (NamedArg (UN x.val) $ PRef fc (UN x.val))
                              $ do tm <- decoratedSymbol fname "=" *> expr pdef fname indents
                                   pure (NamedArg (UN x.val) tm)
               matchAny <- option [] (if isCons list then
                                         do decoratedSymbol fname ","
                                            x <- bounds (decoratedSymbol fname "_")
                                            pure [underscore (boundToFC fname x)]
                                      else fail "non-empty list required")
               end <- bounds (decoratedSymbol fname "}")
               matchAny <- do let fc = boundToFC fname (mergeBounds start end)
                              pure $ if isNil list
                                then [underscore fc]
                                else matchAny
               pure $ matchAny ++ list

        <|> do decoratedSymbol fname "@{"
               commit
               tm <- expr pdef fname indents
               decoratedSymbol fname "}"
               pure [UnnamedAutoArg tm]

  with_ : OriginDesc -> IndentInfo -> Rule PTerm
  with_ fname indents
      = do b <- bounds (do decoratedKeyword fname "with"
                           commit
                           ns <- singleName <|> nameList
                           end <- location
                           rhs <- expr pdef fname indents
                           pure (ns, rhs))
           (ns, rhs) <- pure b.val
           pure (PWithUnambigNames (boundToFC fname b) ns rhs)
    where
      singleName : Rule (List Name)
      singleName = do
        n <- name
        pure [n]

      nameList : Rule (List Name)
      nameList = do
        decoratedSymbol fname "["
        commit
        ns <- sepBy1 (decoratedSymbol fname ",") name
        decoratedSymbol fname "]"
        pure (forget ns)

  opExpr : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  opExpr q fname indents
      = do l <- bounds (appExpr q fname indents)
           (if eqOK q
               then do r <- bounds (continue indents *> decoratedSymbol fname "=" *> opExpr q fname indents)
                       pure $
                         let fc = boundToFC fname (mergeBounds l r)
                             opFC = virtualiseFC fc -- already been highlighted: we don't care
                         in POp fc opFC (UN "=") l.val r.val
               else fail "= not allowed")
             <|>
             (do b <- bounds [| MkPair (continue indents *> bounds iOperator) (opExpr q fname indents) |]
                 (op, r) <- pure b.val
                 let fc = boundToFC fname (mergeBounds l b)
                 let opFC = boundToFC fname op
                 pure (POp fc opFC op.val l.val r))
               <|> pure l.val

  dpairType : OriginDesc -> WithBounds t -> IndentInfo -> Rule PTerm
  dpairType fname start indents
      = do loc <- bounds (do x <- decoratedSimpleBinderName fname
                             decoratedSymbol fname ":"
                             ty <- expr pdef fname indents
                             pure (x, ty))
           (x, ty) <- pure loc.val
           op <- bounds (symbol "**")
           rest <- bounds (nestedDpair fname loc indents <|> expr pdef fname indents)
           pure (PDPair (boundToFC fname (mergeBounds start rest))
                        (boundToFC fname op)
                        (PRef (boundToFC fname loc) (UN x))
                        ty
                        rest.val)

  nestedDpair : OriginDesc -> WithBounds t -> IndentInfo -> Rule PTerm
  nestedDpair fname start indents
      = dpairType fname start indents
    <|> do l <- expr pdef fname indents
           loc <- bounds (symbol "**")
           rest <- bounds (nestedDpair fname loc indents <|> expr pdef fname indents)
           pure (PDPair (boundToFC fname (mergeBounds start rest))
                        (boundToFC fname loc)
                        l
                        (PImplicit (boundToFC fname (mergeBounds start rest)))
                        rest.val)

  bracketedExpr : OriginDesc -> WithBounds t -> IndentInfo -> Rule PTerm
  bracketedExpr fname s indents
      -- left section. This may also be a prefix operator, but we'll sort
      -- that out when desugaring: if the operator is infix, treat it as a
      -- section otherwise treat it as prefix
      = do b <- bounds (do op <- bounds iOperator
                           e <- expr pdef fname indents
                           continueWithDecorated fname indents ")"
                           pure (op, e))
           (op, e) <- pure b.val
           act [(toNonEmptyFC $ boundToFC fname s, Keyword, Nothing)]
           let fc = boundToFC fname (mergeBounds s b)
           let opFC = boundToFC fname op
           pure (PSectionL fc opFC op.val e)
    <|> do  -- (.y.z)  -- section of projection (chain)
           b <- bounds $ forget <$> some (bounds postfixProj)
           decoratedSymbol fname ")"
           act [(toNonEmptyFC $ boundToFC fname s, Keyword, Nothing)]
           let projs = map (\ proj => (boundToFC fname proj, proj.val)) b.val
           pure $ PPostfixAppPartial (boundToFC fname b) projs
      -- unit type/value
    <|> do b <- bounds (continueWith indents ")")
           pure (PUnit (boundToFC fname (mergeBounds s b)))
      -- dependent pairs with type annotation (so, the type form)
    <|> do dpairType fname s indents <* (decorate fname Typ $ symbol ")")
                                     <* act [(toNonEmptyFC $ boundToFC fname s, Typ, Nothing)]
    <|> do e <- bounds (expr pdef fname indents)
           -- dependent pairs with no type annotation
           (do loc <- bounds (symbol "**")
               rest <- bounds ((nestedDpair fname loc indents <|> expr pdef fname indents) <* symbol ")")
               pure (PDPair (boundToFC fname (mergeBounds s rest))
                            (boundToFC fname loc)
                            e.val
                            (PImplicit (boundToFC fname (mergeBounds s rest)))
                            rest.val)) <|>
             -- right sections
             ((do op <- bounds (bounds iOperator <* decoratedSymbol fname ")")
                  act [(toNonEmptyFC $ boundToFC fname s, Keyword, Nothing)]
                  let fc = boundToFC fname (mergeBounds s op)
                  let opFC = boundToFC fname op.val
                  pure (PSectionR fc opFC e.val op.val.val)
               <|>
              -- all the other bracketed expressions
              tuple fname s indents e.val))
    <|> do here <- location
           let fc = MkFC fname here here
           let var = PRef fc (MN "__leftTupleSection" 0)
           ts <- bounds (nonEmptyTuple fname s indents var)
           pure (PLam fc top Explicit var (PInfer fc) ts.val)

  getInitRange : List (WithBounds PTerm) -> EmptyRule (PTerm, Maybe PTerm)
  getInitRange [x] = pure (x.val, Nothing)
  getInitRange [x,y] = pure (x.val, Just y.val)
  getInitRange _ = fatalError "Invalid list range syntax"

  listRange : OriginDesc -> WithBounds t -> IndentInfo -> List (WithBounds PTerm) -> Rule PTerm
  listRange fname s indents xs
      = do b <- bounds (decoratedSymbol fname "]")
           let fc = boundToFC fname (mergeBounds s b)
           rstate <- getInitRange xs
           decorateKeywords fname xs
           pure (PRangeStream fc (fst rstate) (snd rstate))
    <|> do y <- bounds (expr pdef fname indents <* decoratedSymbol fname "]")
           let fc = boundToFC fname (mergeBounds s y)
           rstate <- getInitRange xs
           decorateKeywords fname xs
           pure (PRange fc (fst rstate) (snd rstate) y.val)

  listExpr : OriginDesc -> WithBounds () -> IndentInfo -> Rule PTerm
  listExpr fname s indents
      = do b <- bounds (do ret <- expr pnowith fname indents
                           decoratedSymbol fname "|"
                           conds <- sepBy1 (decoratedSymbol fname ",") (doAct fname indents)
                           decoratedSymbol fname "]"
                           pure (ret, conds))
           (ret, conds) <- pure b.val
           pure (PComprehension (boundToFC fname (mergeBounds s b)) ret (concat conds))
    <|> do xs <- option [] $ do
                     hd <- expr pdef fname indents
                     tl <- many $ do b <- bounds (symbol ",")
                                     x <- expr pdef fname indents
                                     pure (x <$ b)
                     pure ((hd <$ s) :: tl)
           (do decoratedSymbol fname ".."
               listRange fname s indents xs)
             <|> (do b <- bounds (symbol "]")
                     pure $
                       let fc = boundToFC fname (mergeBounds s b)
                           nilFC = if null xs then fc else boundToFC fname b
                       in PList fc nilFC (map (\ t => (boundToFC fname t, t.val)) xs))

  snocListExpr : OriginDesc -> WithBounds () -> IndentInfo -> Rule PTerm
  snocListExpr fname s indents
      = {- TODO: comprehension -}
        do mHeadTail <- optional $ do
             hd <- many $ do x <- expr pdef fname indents
                             b <- bounds (symbol ",")
                             pure (x <$ b)
             tl <- expr pdef fname indents
             pure (hd, tl)
           {- TODO: reverse ranges -}
           b <- bounds (symbol "]")
           pure $
             let xs : List (WithBounds PTerm)
                    = case mHeadTail of
                        Nothing      => []
                        Just (hd,tl) => hd ++ [ tl <$ b]
                 fc = boundToFC fname (mergeBounds s b)
                 nilFC = ifThenElse (null xs) fc (boundToFC fname s)
             in PSnocList fc nilFC (map (\ t => (boundToFC fname t, t.val)) xs) --)

  nonEmptyTuple : OriginDesc -> WithBounds t -> IndentInfo -> PTerm -> Rule PTerm
  nonEmptyTuple fname s indents e
      = do vals <- some $ do b <- bounds (symbol ",")
                             exp <- optional (expr pdef fname indents)
                             pure (boundToFC fname b, exp)
           end <- continueWithDecorated fname indents ")"
           act [(toNonEmptyFC (boundToFC fname s), Keyword, Nothing)]
           pure $ let (start ::: rest) = vals in
                  buildOutput (fst start) (mergePairs 0 start rest)
    where

      lams : List (FC, PTerm) -> PTerm -> PTerm
      lams [] e = e
      lams ((fc, var) :: vars) e
        = let vfc = virtualiseFC fc in
          PLam vfc top Explicit var (PInfer vfc) $ lams vars e

      buildOutput : FC -> (List (FC, PTerm), PTerm) -> PTerm
      buildOutput fc (vars, scope) = lams vars $ PPair fc e scope

      optionalPair : Int ->
                     (FC, Maybe PTerm) -> (Int, (List (FC, PTerm), PTerm))
      optionalPair i (fc, Just e)  = (i, ([], e))
      optionalPair i (fc, Nothing) =
        let var = PRef fc (MN "__infixTupleSection" i) in
        (i+1, ([(fc, var)], var))

      mergePairs : Int -> (FC, Maybe PTerm) ->
                   List (FC, Maybe PTerm) -> (List (FC, PTerm), PTerm)
      mergePairs i hd [] = snd (optionalPair i hd)
      mergePairs i hd (exp :: rest)
          = let (j, (var, t)) = optionalPair i hd in
            let (vars, ts)    = mergePairs j exp rest in
            (var ++ vars, PPair (fst exp) t ts)

  -- A pair, dependent pair, or just a single expression
  tuple : OriginDesc -> WithBounds t -> IndentInfo -> PTerm -> Rule PTerm
  tuple fname s indents e
     =   nonEmptyTuple fname s indents e
     <|> do end <- bounds (continueWithDecorated fname indents ")")
            act [(toNonEmptyFC $ boundToFC fname s, Keyword, Nothing)]
            pure (PBracketed (boundToFC fname (mergeBounds s end)) e)

  simpleExpr : OriginDesc -> IndentInfo -> Rule PTerm
  simpleExpr fname indents
    = do  -- x.y.z
          b <- bounds (do root <- simplerExpr fname indents
                          projs <- many (bounds postfixProj)
                          pure (root, projs))
          (root, projs) <- pure b.val
          let projs = map (\ proj => (boundToFC fname proj, proj.val)) projs
          pure $ case projs of
            [] => root
            _  => PPostfixApp (boundToFC fname b) root projs
    <|> do b <- bounds (forget <$> some (bounds postfixProj))
           pure $ let projs = map (\ proj => (boundToFC fname proj, proj.val)) b.val in
                  PPostfixAppPartial (boundToFC fname b) projs

  simplerExpr : OriginDesc -> IndentInfo -> Rule PTerm
  simplerExpr fname indents
      = do b <- bounds (do x <- bounds (decoratedSimpleBinderName fname)
                           decoratedSymbol fname "@"
                           commit
                           expr <- simpleExpr fname indents
                           pure (x, expr))
           (x, expr) <- pure b.val
           pure (PAs (boundToFC fname b) (boundToFC fname x) (UN x.val) expr)
    <|> atom fname
    <|> binder fname indents
    <|> rewrite_ fname indents
    <|> record_ fname indents
    <|> singlelineStr pdef fname indents
    <|> multilineStr pdef fname indents
    <|> do b <- bounds (decoratedSymbol fname ".(" *> commit *> expr pdef fname indents <* decoratedSymbol fname ")")
           pure (PDotted (boundToFC fname b) b.val)
    <|> do b <- bounds (decoratedSymbol fname "`(" *> expr pdef fname indents <* decoratedSymbol fname ")")
           pure (PQuote (boundToFC fname b) b.val)
    <|> do b <- bounds (decoratedSymbol fname "`{{" *> name <* decoratedSymbol fname "}}")
           pure (PQuoteName (boundToFC fname b) b.val)
    <|> do b <- bounds (decoratedSymbol fname "`[" *> nonEmptyBlock (topDecl fname) <* decoratedSymbol fname "]")
           pure (PQuoteDecl (boundToFC fname b) (collectDefs (concat b.val)))
    <|> do b <- bounds (decoratedSymbol fname "~" *> simpleExpr fname indents)
           pure (PUnquote (boundToFC fname b) b.val)
    <|> do start <- bounds (symbol "(")
           bracketedExpr fname start indents
    <|> do start <- bounds (symbol "[<")
           snocListExpr fname start indents
    <|> do start <- bounds (symbol "[>" <|> symbol "[")
           listExpr fname start indents
    <|> do b <- bounds (decoratedSymbol fname "!" *> simpleExpr fname indents)
           pure (PBang (virtualiseFC $ boundToFC fname b) b.val)
    <|> do b <- bounds (decoratedSymbol fname "[|" *> expr pdef fname indents <* decoratedSymbol fname "|]")
           pure (PIdiom (boundToFC fname b) b.val)
    <|> do b <- bounds (pragma "runElab" *> expr pdef fname indents)
           pure (PRunElab (boundToFC fname b) b.val)
    <|> do b <- bounds $ do pragma "logging"
                            topic <- optional (split (('.') ==) <$> simpleStr)
                            lvl   <- intLit
                            e     <- expr pdef fname indents
                            pure (MkPair (mkLogLevel' topic (integerToNat lvl)) e)
           (lvl, e) <- pure b.val
           pure (PUnifyLog (boundToFC fname b) lvl e)

  multiplicity : OriginDesc -> EmptyRule RigCount
  multiplicity fname
      = case !(optional $ decorate fname Keyword intLit) of
          (Just 0) => pure erased
          (Just 1) => pure linear
          Nothing => pure top
          _ => fail "Invalid multiplicity (must be 0 or 1)"

  pibindAll : OriginDesc -> PiInfo PTerm ->
              List (RigCount, WithBounds (Maybe Name), PTerm) ->
              PTerm -> PTerm
  pibindAll fname p [] scope = scope
  pibindAll fname p ((rig, n, ty) :: rest) scope
           = PPi (boundToFC fname n) rig p (n.val) ty (pibindAll fname p rest scope)

  bindList : OriginDesc -> IndentInfo ->
             Rule (List (RigCount, WithBounds PTerm, PTerm))
  bindList fname indents
      = forget <$> sepBy1 (decoratedSymbol fname ",")
                          (do rig <- multiplicity fname
                              pat <- bounds (simpleExpr fname indents)
                              ty <- option
                                       (PInfer (boundToFC fname pat))
                                       (decoratedSymbol fname ":" *> opExpr pdef fname indents)
                              pure (rig, pat, ty))

  pibindListName : OriginDesc -> IndentInfo ->
                   Rule (List (RigCount, WithBounds Name, PTerm))
  pibindListName fname indents
       = do rig <- multiplicity fname
            ns <- sepBy1 (decoratedSymbol fname ",") (bounds binderName)
            let ns = forget $ map (map UN) ns
            decorateBoundedNames fname Bound ns
            decoratedSymbol fname ":"
            ty <- expr pdef fname indents
            atEnd indents
            pure (map (\n => (rig, n, ty)) ns)
     <|> forget <$> sepBy1 (decoratedSymbol fname ",")
                           (do rig <- multiplicity fname
                               n <- bounds (decorate fname Bound binderName)
                               decoratedSymbol fname ":"
                               ty <- expr pdef fname indents
                               pure (rig, map UN n, ty))
    where
      -- _ gets treated specially here, it means "I don't care about the name"
      binderName : Rule String
      binderName = unqualifiedName <|> (symbol "_" $> "_")

  pibindList : OriginDesc -> IndentInfo ->
               Rule (List (RigCount, WithBounds (Maybe Name), PTerm))
  pibindList fname indents
    = do params <- pibindListName fname indents
         pure $ map (\(rig, n, ty) => (rig, map Just n, ty)) params

  bindSymbol : OriginDesc -> Rule (PiInfo PTerm)
  bindSymbol fname
      = (decoratedSymbol fname "->" $> Explicit)
    <|> (decoratedSymbol fname "=>" $> AutoImplicit)

  explicitPi : OriginDesc -> IndentInfo -> Rule PTerm
  explicitPi fname indents
      = do decoratedSymbol fname "("
           binders <- pibindList fname indents
           decoratedSymbol fname ")"
           exp <- bindSymbol fname
           scope <- mustWork $ typeExpr pdef fname indents
           pure (pibindAll fname exp binders scope)

  autoImplicitPi : OriginDesc -> IndentInfo -> Rule PTerm
  autoImplicitPi fname indents
      = do decoratedSymbol fname "{"
           decoratedKeyword fname "auto"
           commit
           binders <- pibindList fname indents
           decoratedSymbol fname "}"
           decoratedSymbol fname "->"
           scope <- mustWork $ typeExpr pdef fname indents
           pure (pibindAll fname AutoImplicit binders scope)

  defaultImplicitPi : OriginDesc -> IndentInfo -> Rule PTerm
  defaultImplicitPi fname indents
      = do decoratedSymbol fname "{"
           decoratedKeyword fname "default"
           commit
           t <- simpleExpr fname indents
           binders <- pibindList fname indents
           decoratedSymbol fname "}"
           decoratedSymbol fname "->"
           scope <- mustWork $ typeExpr pdef fname indents
           pure (pibindAll fname (DefImplicit t) binders scope)

  forall_ : OriginDesc -> IndentInfo -> Rule PTerm
  forall_ fname indents
      = do decoratedKeyword fname "forall"
           commit
           ns <- sepBy1 (decoratedSymbol fname ",")
                        (bounds (decoratedSimpleBinderName fname))
           let binders = map (\n => ( erased {a=RigCount}
                                    , map (Just . UN) n
                                    , PImplicit (boundToFC fname n))
                                    ) (forget ns)
           decoratedSymbol fname "."
           scope <- mustWork $ typeExpr pdef fname indents
           pure (pibindAll fname Implicit binders scope)

  implicitPi : OriginDesc -> IndentInfo -> Rule PTerm
  implicitPi fname indents
      = do decoratedSymbol fname "{"
           binders <- pibindList fname indents
           decoratedSymbol fname "}"
           decoratedSymbol fname "->"
           scope <- mustWork $ typeExpr pdef fname indents
           pure (pibindAll fname Implicit binders scope)

  lam : OriginDesc -> IndentInfo -> Rule PTerm
  lam fname indents
      = do decoratedSymbol fname "\\"
           commit
           switch <- optional (bounds $ decoratedKeyword fname "case")
           case switch of
             Nothing => continueLam
             Just r  => continueLamCase r

     where

       bindAll : List (RigCount, WithBounds PTerm, PTerm) -> PTerm -> PTerm
       bindAll [] scope = scope
       bindAll ((rig, pat, ty) :: rest) scope
           = PLam (boundToFC fname pat) rig Explicit pat.val ty
                  (bindAll rest scope)

       continueLam : Rule PTerm
       continueLam = do
           binders <- bindList fname indents
           decoratedSymbol fname "=>"
           mustContinue indents Nothing
           scope <- expr pdef fname indents
           pure (bindAll binders scope)

       continueLamCase : WithBounds () -> Rule PTerm
       continueLamCase endCase = do
           b <- bounds (forget <$> nonEmptyBlock (caseAlt fname))
           pure
            (let fc = boundToFC fname b
                 fcCase = virtualiseFC $ boundToFC fname endCase
                 n = MN "lcase" 0 in
              PLam fcCase top Explicit (PRef fcCase n) (PInfer fcCase) $
                PCase (virtualiseFC fc) (PRef fcCase n) b.val)

  letBlock : OriginDesc -> IndentInfo -> Rule (WithBounds (Either LetBinder LetDecl))
  letBlock fname indents = bounds (letBinder <||> letDecl) where

    letBinder : Rule LetBinder
    letBinder = do s <- bounds (MkPair <$> multiplicity fname <*> expr plhs fname indents)
                   (rig, pat) <- pure s.val
                   ty <- option (PImplicit (virtualiseFC $ boundToFC fname s))
                                (decoratedSymbol fname ":" *> typeExpr (pnoeq pdef) fname indents)
                   (decoratedSymbol fname "=" <|> decoratedSymbol fname ":=")
                   val <- expr pnowith fname indents
                   alts <- block (patAlt fname)
                   pure (MkLetBinder rig pat ty val alts)

    letDecl : Rule LetDecl
    letDecl = collectDefs . concat <$> nonEmptyBlock (try . topDecl fname)

  let_ : OriginDesc -> IndentInfo -> Rule PTerm
  let_ fname indents
      = do decoratedKeyword fname "let"
           commit
           res <- nonEmptyBlock (letBlock fname)
           commitKeyword fname indents "in"
           scope <- typeExpr pdef fname indents
           pure (mkLets fname res scope)

  case_ : OriginDesc -> IndentInfo -> Rule PTerm
  case_ fname indents
      = do b <- bounds (do decoratedKeyword fname "case"
                           scr <- expr pdef fname indents
                           mustWork (commitKeyword fname indents "of")
                           alts <- block (caseAlt fname)
                           pure (scr, alts))
           (scr, alts) <- pure b.val
           pure (PCase (virtualiseFC $ boundToFC fname b) scr alts)


  caseAlt : OriginDesc -> IndentInfo -> Rule PClause
  caseAlt fname indents
      = do lhs <- bounds (opExpr plhs fname indents)
           caseRHS fname lhs indents lhs.val

  caseRHS : OriginDesc -> WithBounds t -> IndentInfo -> PTerm -> Rule PClause
  caseRHS fname start indents lhs
      = do rhs <- bounds (decoratedSymbol fname "=>" *> mustContinue indents Nothing *> expr pdef fname indents)
           atEnd indents
           let fc = boundToFC fname (mergeBounds start rhs)
           pure (MkPatClause fc lhs rhs.val [])
    <|> do end <- bounds (decoratedKeyword fname "impossible")
           atEnd indents
           pure (MkImpossible (boundToFC fname (mergeBounds start end)) lhs)

  if_ : OriginDesc -> IndentInfo -> Rule PTerm
  if_ fname indents
      = do b <- bounds (do decoratedKeyword fname "if"
                           x <- expr pdef fname indents
                           commitKeyword fname indents "then"
                           t <- expr pdef fname indents
                           commitKeyword fname indents "else"
                           e <- expr pdef fname indents
                           pure (x, t, e))
           atEnd indents
           (x, t, e) <- pure b.val
           pure (PIfThenElse (boundToFC fname b) x t e)

  record_ : OriginDesc -> IndentInfo -> Rule PTerm
  record_ fname indents
      = do b <- bounds (do kw <- option False
                                 (decoratedKeyword fname "record"
                                   $> True) -- TODO deprecated
                           decoratedSymbol fname "{"
                           commit
                           fs <- sepBy1 (decoratedSymbol fname ",") (field kw fname indents)
                           decoratedSymbol fname "}"
                           pure $ forget fs)
           pure (PUpdate (boundToFC fname b) b.val)

  field : Bool -> OriginDesc -> IndentInfo -> Rule PFieldUpdate
  field kw fname indents
      = do path <- map fieldName <$> [| decorate fname Function name :: many recFieldCompat |]
           upd <- (ifThenElse kw (decoratedSymbol fname "=") (decoratedSymbol fname ":=") $> PSetField)
                      <|>
                  (decoratedSymbol fname "$=" $> PSetFieldApp)
           val <- opExpr plhs fname indents
           pure (upd path val)
    where
      fieldName : Name -> String
      fieldName (UN s) = s
      fieldName (RF s) = s
      fieldName _ = "_impossible"

      -- this allows the dotted syntax .field
      -- but also the arrowed syntax ->field for compatibility with Idris 1
      recFieldCompat : Rule Name
      recFieldCompat = decorate fname Function postfixProj
                  <|> (decoratedSymbol fname "->"
                       *> decorate fname Function name)

  rewrite_ : OriginDesc -> IndentInfo -> Rule PTerm
  rewrite_ fname indents
      = do b <- bounds (do decoratedKeyword fname "rewrite"
                           rule <- expr pdef fname indents
                           commitKeyword fname indents "in"
                           tm <- expr pdef fname indents
                           pure (rule, tm))
           (rule, tm) <- pure b.val
           pure (PRewrite (boundToFC fname b) rule tm)

  doBlock : OriginDesc -> IndentInfo -> Rule PTerm
  doBlock fname indents
      = do b <- bounds $ keyword "do" *> block (doAct fname)
           commit
           pure (PDoBlock (virtualiseFC $ boundToFC fname b) Nothing (concat b.val))
    <|> do nsdo <- bounds namespacedIdent
           -- TODO: need to attach metadata correctly here
           the (EmptyRule PTerm) $ case nsdo.val of
                (ns, "do") =>
                   do commit
                      actions <- Core.bounds (block (doAct fname))
                      let fc = virtualiseFC $
                               boundToFC fname (mergeBounds nsdo actions)
                      pure (PDoBlock fc ns (concat actions.val))
                _ => fail "Not a namespaced 'do'"

  validPatternVar : Name -> EmptyRule ()
  validPatternVar (UN n)
      = if lowerFirst n then pure ()
                        else fail "Not a pattern variable"
  validPatternVar _ = fail "Not a pattern variable"

  doAct : OriginDesc -> IndentInfo -> Rule (List PDo)
  doAct fname indents
      = do b <- bounds (do n <- bounds name
                           -- If the name doesn't begin with a lower case letter, we should
                           -- treat this as a pattern, so fail
                           validPatternVar n.val
                           decoratedSymbol fname "<-"
                           val <- expr pdef fname indents
                           pure (n, val))
           atEnd indents
           let (n, val) = b.val
           pure [DoBind (boundToFC fname b) (boundToFC fname n) n.val val]
    <|> do decoratedKeyword fname "let"
           commit
           res <- nonEmptyBlock (letBlock fname)
           atEnd indents
           pure (mkDoLets fname res)
    <|> do b <- bounds (decoratedKeyword fname "rewrite" *> expr pdef fname indents)
           atEnd indents
           pure [DoRewrite (boundToFC fname b) b.val]
    <|> do e <- bounds (expr plhs fname indents)
           (atEnd indents $> [DoExp (virtualiseFC $ boundToFC fname e) e.val])
             <|> (do b <- bounds $ decoratedSymbol fname "<-" *> [| (expr pnowith fname indents, block (patAlt fname)) |]
                     atEnd indents
                     let (v, alts) = b.val
                     let fc = virtualiseFC $ boundToFC fname (mergeBounds e b)
                     pure [DoBindPat fc e.val v alts])

  patAlt : OriginDesc -> IndentInfo -> Rule PClause
  patAlt fname indents
      = do decoratedSymbol fname "|"
           caseAlt fname indents

  lazy : OriginDesc -> IndentInfo -> Rule PTerm
  lazy fname indents
      = do tm <- bounds (decorate fname Typ (exactIdent "Lazy")
                         *> simpleExpr fname indents)
           pure (PDelayed (boundToFC fname tm) LLazy tm.val)
    <|> do tm <- bounds (decorate fname Typ (exactIdent "Inf")
                         *> simpleExpr fname indents)
           pure (PDelayed (boundToFC fname tm) LInf tm.val)
    <|> do tm <- bounds (decorate fname Data (exactIdent "Delay")
                         *> simpleExpr fname indents)
           pure (PDelay (boundToFC fname tm) tm.val)
    <|> do tm <- bounds (decorate fname Data (exactIdent "Force")
                         *> simpleExpr fname indents)
           pure (PForce (boundToFC fname tm) tm.val)

  binder : OriginDesc -> IndentInfo -> Rule PTerm
  binder fname indents
      = let_ fname indents
    <|> autoImplicitPi fname indents
    <|> defaultImplicitPi fname indents
    <|> forall_ fname indents
    <|> implicitPi fname indents
    <|> explicitPi fname indents
    <|> lam fname indents

  typeExpr : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  typeExpr q fname indents
      = do arg <- bounds (opExpr q fname indents)
           (do continue indents
               rest <- some [| (bindSymbol fname, bounds $ opExpr pdef fname indents) |]
               pure (mkPi arg (forget rest)))
             <|> pure arg.val
    where
      mkPi : WithBounds PTerm -> List (PiInfo PTerm, WithBounds PTerm) -> PTerm
      mkPi arg [] = arg.val
      mkPi arg ((exp, a) :: as)
            = PPi (boundToFC fname arg) top exp Nothing arg.val
                  (mkPi a as)

  export
  expr : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  expr = typeExpr

  interpBlock : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  interpBlock q fname idents = interpBegin *> (mustWork $ expr q fname idents) <* interpEnd

  export
  singlelineStr : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  singlelineStr q fname idents
      = decorate fname Data $
        do b <- bounds $ do begin <- bounds strBegin
                            commit
                            xs <- many $ bounds $ (interpBlock q fname idents) <||> strLitLines
                            pstrs <- case traverse toPStr xs of
                                          Left err => fatalLoc begin.bounds err
                                          Right pstrs => pure $ pstrs
                            strEnd
                            pure pstrs
           pure $ PString (boundToFC fname b) b.val
    where
      toPStr : (WithBounds $ Either PTerm (List1 String)) -> Either String PStr
      toPStr x = case x.val of
                      Right (str:::[]) => Right $ StrLiteral (boundToFC fname x) str
                      Right (_:::strs) => Left "Multi-line string is expected to begin with \"\"\""
                      Left tm => Right $ StrInterp (boundToFC fname x) tm

  export
  multilineStr : ParseOpts -> OriginDesc -> IndentInfo -> Rule PTerm
  multilineStr q fname idents
      = decorate fname Data $
        do b <- bounds $ do multilineBegin
                            commit
                            xs <- many $ bounds $ (interpBlock q fname idents) <||> strLitLines
                            endloc <- location
                            strEnd
                            pure (endloc, toLines xs [] [])
           pure $ let ((_, col), xs) = b.val in
                      PMultiline (boundToFC fname b) (fromInteger $ cast col) xs
    where
      toLines : List (WithBounds $ Either PTerm (List1 String)) -> List PStr -> List (List PStr) -> List (List PStr)
      toLines [] line acc = acc `snoc` line
      toLines (x::xs) line acc
          = case x.val of
                 Left tm => toLines xs (line `snoc` (StrInterp (boundToFC fname x) tm)) acc
                 Right (str:::[]) => toLines xs (line `snoc` (StrLiteral (boundToFC fname x) str)) acc
                 Right (str:::strs@(_::_)) => toLines xs [StrLiteral (boundToFC fname x) (last strs)]
                                                         ((acc `snoc` (line `snoc` (StrLiteral (boundToFC fname x) str))) ++
                                                               ((\str => [StrLiteral (boundToFC fname x) str]) <$> (init strs)))

visOption : OriginDesc ->  Rule Visibility
visOption fname
    = (decoratedKeyword fname "public" *> decoratedKeyword fname "export" $> Public)
  <|> (decoratedKeyword fname "export" $> Export)
  <|> (decoratedKeyword fname "private" $> Private)

visibility : OriginDesc -> EmptyRule Visibility
visibility fname
    = visOption fname
  <|> pure Private

tyDecls : Rule Name -> String -> OriginDesc -> IndentInfo -> Rule (List1 PTypeDecl)
tyDecls declName predoc fname indents
    = do bs <- do docns <- sepBy1 (decoratedSymbol fname ",") [| (option "" documentation, bounds declName) |]
                  decoratedSymbol fname ":"
                  mustWork $ do ty  <- expr pdef fname indents
                                pure $ map (\(doc, n) => (doc, n.val, boundToFC fname n, ty))
                                           docns
         atEnd indents
         pure $ map (\(doc, n, nFC, ty) => (MkPTy nFC nFC n (predoc ++ doc) ty))
                    bs

withFlags : EmptyRule (List WithFlag)
withFlags
    = pragma "syntactic" *> (Syntactic ::) <$> withFlags
  <|> pure []

mutual
  parseRHS : (withArgs : Nat) ->
             OriginDesc -> WithBounds t -> Int ->
             IndentInfo -> (lhs : PTerm) -> Rule PClause
  parseRHS withArgs fname start col indents lhs
       = do b <- bounds $ decoratedSymbol fname "=" *> mustWork [| (expr pdef fname indents, option [] $ whereBlock fname col) |]
            atEnd indents
            (rhs, ws) <- pure b.val
            let fc = boundToFC fname (mergeBounds start b)
            pure (MkPatClause fc lhs rhs ws)
     <|> do b <- bounds (do decoratedKeyword fname "with"
                            commit
                            flags <- withFlags
                            start <- bounds (decoratedSymbol fname "(")
                            wval <- bracketedExpr fname start indents
                            prf <- optional (decoratedKeyword fname "proof"
                                             *> UN <$> decoratedSimpleBinderName fname)
                            ws <- mustWork $ nonEmptyBlockAfter col (clause (S withArgs) fname)
                            pure (prf, flags, wval, forget ws))
            (prf, flags, wval, ws) <- pure b.val
            let fc = boundToFC fname (mergeBounds start b)
            pure (MkWithClause fc lhs wval prf flags ws)
     <|> do end <- bounds (decoratedKeyword fname "impossible")
            atEnd indents
            pure (MkImpossible (boundToFC fname (mergeBounds start end)) lhs)

  clause : Nat -> OriginDesc -> IndentInfo -> Rule PClause
  clause withArgs fname indents
      = do b <- bounds (do col <- column
                           lhs <- expr plhs fname indents
                           extra <- many parseWithArg
                           pure (col, lhs, extra))
           (col, lhs, extra) <- pure b.val
           -- Can't have the dependent 'if' here since we won't be able
           -- to infer the termination status of the rule
           ifThenElse (withArgs /= length extra)
              (fatalError $ "Wrong number of 'with' arguments:"
                         ++ " expected " ++ show withArgs
                         ++ " but got " ++ show (length extra))
              (parseRHS withArgs fname b col indents (applyArgs lhs extra))
    where
      applyArgs : PTerm -> List (FC, PTerm) -> PTerm
      applyArgs f [] = f
      applyArgs f ((fc, a) :: args) = applyArgs (PApp fc f a) args

      parseWithArg : Rule (FC, PTerm)
      parseWithArg
          = do decoratedSymbol fname "|"
               tm <- bounds (expr plhs fname indents)
               pure (boundToFC fname tm, tm.val)

mkTyConType : OriginDesc -> FC -> List (WithBounds Name) -> PTerm
mkTyConType fname fc [] = PType (virtualiseFC fc)
mkTyConType fname fc (x :: xs)
   = let bfc = boundToFC fname x in
     PPi bfc top Explicit Nothing (PType (virtualiseFC fc))
     $ mkTyConType fname fc xs

mkDataConType : FC -> PTerm -> List ArgType -> Maybe PTerm
mkDataConType fc ret [] = Just ret
mkDataConType fc ret (UnnamedExpArg x :: xs)
    = PPi fc top Explicit Nothing x <$> mkDataConType fc ret xs
mkDataConType fc ret (UnnamedAutoArg x :: xs)
    = PPi fc top AutoImplicit Nothing x <$> mkDataConType fc ret xs
mkDataConType _ _ _ -- with and named applications not allowed in simple ADTs
    = Nothing

simpleCon : OriginDesc -> PTerm -> IndentInfo -> Rule PTypeDecl
simpleCon fname ret indents
    = do b <- bounds (do cdoc   <- option "" documentation
                         cname  <- bounds $ decoratedDataConstructorName fname
                         params <- many (argExpr plhs fname indents)
                         pure (cdoc, cname.val, boundToFC fname cname, params))
         atEnd indents
         (cdoc, cname, cnameFC, params) <- pure b.val
         let cfc = boundToFC fname b
         fromMaybe (fatalError "Named arguments not allowed in ADT constructors")
                   (pure . MkPTy cfc cnameFC cname cdoc <$> mkDataConType cfc ret (concat params))

simpleData : OriginDesc -> WithBounds t ->
             WithBounds Name -> IndentInfo -> Rule PDataDecl
simpleData fname start tyName indents
    = do b <- bounds (do params <- many (bounds $ decorate fname Bound name)
                         tyend <- bounds (decoratedSymbol fname "=")
                         let tyfc = boundToFC fname (mergeBounds start tyend)
                         let tyCon = PRef (boundToFC fname tyName) tyName.val
                         let toPRef = \ t => PRef (boundToFC fname t) t.val
                         let conRetTy = papply tyfc tyCon (map toPRef params)
                         cons <- sepBy1 (decoratedSymbol fname "|") (simpleCon fname conRetTy indents)
                         pure (params, tyfc, forget cons))
         (params, tyfc, cons) <- pure b.val
         pure (MkPData (boundToFC fname (mergeBounds start b)) tyName.val
                       (mkTyConType fname tyfc params) [] cons)

dataOpt : Rule DataOpt
dataOpt
    = (exactIdent "noHints" $> NoHints)
  <|> (exactIdent "uniqueSearch" $> UniqueSearch)
  <|> (exactIdent "search" *> SearchBy <$> forget <$> some name)
  <|> (exactIdent "external" $> External)
  <|> (exactIdent "noNewtype" $> NoNewtype)

dataBody : OriginDesc -> Int -> WithBounds t -> Name -> IndentInfo -> PTerm ->
          EmptyRule PDataDecl
dataBody fname mincol start n indents ty
    = do atEndIndent indents
         pure (MkPLater (boundToFC fname start) n ty)
  <|> do b <- bounds (do decoratedKeyword fname "where"
                         opts <- option [] $ decoratedSymbol fname "[" *> forget <$> sepBy1 (decoratedSymbol fname ",") dataOpt <* decoratedSymbol fname "]"
                         cs <- blockAfter mincol (tyDecls (mustWork $ decoratedDataConstructorName fname) "" fname)
                         pure (opts, concatMap forget cs))
         (opts, cs) <- pure b.val
         pure (MkPData (boundToFC fname (mergeBounds start b)) n ty opts cs)

gadtData : OriginDesc -> Int -> WithBounds t ->
           WithBounds Name -> IndentInfo -> Rule PDataDecl
gadtData fname mincol start tyName indents
    = do decoratedSymbol fname ":"
         commit
         ty <- expr pdef fname indents
         dataBody fname mincol start tyName.val indents ty

dataDeclBody : OriginDesc -> IndentInfo -> Rule PDataDecl
dataDeclBody fname indents
    = do b <- bounds (do col <- column
                         decoratedKeyword fname "data"
                         n <- mustWork (bounds $ decoratedDataTypeName fname)
                         pure (col, n))
         (col, n) <- pure b.val
         simpleData fname b n indents <|> gadtData fname col b n indents

dataDecl : OriginDesc -> IndentInfo -> Rule PDecl
dataDecl fname indents
    = do b <- bounds (do doc   <- option "" documentation
                         vis   <- visibility fname
                         dat   <- dataDeclBody fname indents
                         pure (doc, vis, dat))
         (doc, vis, dat) <- pure b.val
         pure (PData (boundToFC fname b) doc vis dat)

stripBraces : String -> String
stripBraces str = pack (drop '{' (reverse (drop '}' (reverse (unpack str)))))
  where
    drop : Char -> List Char -> List Char
    drop c [] = []
    drop c (c' :: xs) = if c == c' then drop c xs else c' :: xs

onoff : Rule Bool
onoff
   = (exactIdent "on" $> True)
 <|> (exactIdent "off" $> False)

extension : Rule LangExt
extension
    = (exactIdent "ElabReflection" $> ElabReflection)
  <|> (exactIdent "Borrowing" $> Borrowing)

totalityOpt : OriginDesc -> Rule TotalReq
totalityOpt fname
    = (decoratedKeyword fname "partial" $> PartialOK)
  <|> (decoratedKeyword fname "total" $> Total)
  <|> (decoratedKeyword fname "covering" $> CoveringOnly)

logLevel : Rule (Maybe LogLevel)
logLevel
  = (Nothing <$ exactIdent "off")
    <|> do topic <- optional (split ('.' ==) <$> simpleStr)
           lvl <- intLit
           pure (Just (mkLogLevel' topic (fromInteger lvl)))
    <|> fail "expected a log level"

directive : OriginDesc -> IndentInfo -> Rule Directive
directive fname indents
    = do decorate fname Keyword $ pragma "hide"
         n <- name
         atEnd indents
         pure (Hide n)
--   <|> do pragma "hide_export"
--          n <- name
--          atEnd indents
--          pure (Hide True n)
  <|> do decorate fname Keyword $ pragma "logging"
         lvl <- logLevel
         atEnd indents
         pure (Logging lvl)
  <|> do decorate fname Keyword $ pragma "auto_lazy"
         b <- onoff
         atEnd indents
         pure (LazyOn b)
  <|> do decorate fname Keyword $ pragma "unbound_implicits"
         b <- onoff
         atEnd indents
         pure (UnboundImplicits b)
  <|> do decorate fname Keyword $ pragma "prefix_record_projections"
         b <- onoff
         atEnd indents
         pure (PrefixRecordProjections b)
  <|> do decorate fname Keyword $ pragma "ambiguity_depth"
         lvl <- decorate fname Keyword $ intLit
         atEnd indents
         pure (AmbigDepth (fromInteger lvl))
  <|> do decorate fname Keyword $ pragma "auto_implicit_depth"
         dpt <- decorate fname Keyword $ intLit
         atEnd indents
         pure (AutoImplicitDepth (fromInteger dpt))
  <|> do decorate fname Keyword $ pragma "nf_metavar_threshold"
         dpt <- decorate fname Keyword $ intLit
         atEnd indents
         pure (NFMetavarThreshold (fromInteger dpt))
  <|> do decorate fname Keyword $ pragma "search_timeout"
         t <- decorate fname Keyword $ intLit
         atEnd indents
         pure (SearchTimeout t)
  <|> do decorate fname Keyword $ pragma "pair"
         ty <- name
         f <- name
         s <- name
         atEnd indents
         pure (PairNames ty f s)
  <|> do decorate fname Keyword $ pragma "rewrite"
         eq <- name
         rw <- name
         atEnd indents
         pure (RewriteName eq rw)
  <|> do decorate fname Keyword $ pragma "integerLit"
         n <- name
         atEnd indents
         pure (PrimInteger n)
  <|> do decorate fname Keyword $ pragma "stringLit"
         n <- name
         atEnd indents
         pure (PrimString n)
  <|> do decorate fname Keyword $ pragma "charLit"
         n <- name
         atEnd indents
         pure (PrimChar n)
  <|> do decorate fname Keyword $ pragma "doubleLit"
         n <- name
         atEnd indents
         pure (PrimDouble n)
  <|> do decorate fname Keyword $ pragma "name"
         n <- name
         ns <- sepBy1 (decoratedSymbol fname ",")
                       (decoratedSimpleBinderName fname)
         atEnd indents
         pure (Names n (forget ns))
  <|> do decorate fname Keyword $ pragma "pattern_synonym"
         n <- name
         atEnd indents
         pure (PatternSynonym n)
  <|> do decorate fname Keyword $ pragma "start"
         e <- expr pdef fname indents
         atEnd indents
         pure (StartExpr e)
  <|> do decorate fname Keyword $ pragma "allow_overloads"
         n <- name
         atEnd indents
         pure (Overloadable n)
  <|> do decorate fname Keyword $ pragma "language"
         e <- extension
         atEnd indents
         pure (Extension e)
  <|> do decorate fname Keyword $ pragma "default"
         tot <- totalityOpt fname
         atEnd indents
         pure (DefaultTotality tot)

fix : Rule Fixity
fix
    = (keyword "infixl" $> InfixL)
  <|> (keyword "infixr" $> InfixR)
  <|> (keyword "infix"  $> Infix)
  <|> (keyword "prefix" $> Prefix)

namespaceHead : Rule Namespace
namespaceHead = keyword "namespace" *> mustWork namespaceId

namespaceDecl : OriginDesc -> IndentInfo -> Rule PDecl
namespaceDecl fname indents
    = do b <- bounds (do doc   <- option "" documentation
                         col   <- column
                         ns    <- namespaceHead
                         ds    <- blockAfter col (topDecl fname)
                         pure (doc, ns, ds))
         (doc, ns, ds) <- pure b.val
         pure (PNamespace (boundToFC fname b) ns (collectDefs $ concat ds))

transformDecl : OriginDesc -> IndentInfo -> Rule PDecl
transformDecl fname indents
    = do b <- bounds (do pragma "transform"
                         n <- simpleStr
                         lhs <- expr plhs fname indents
                         decoratedSymbol fname "="
                         rhs <- expr pnowith fname indents
                         pure (n, lhs, rhs))
         (n, lhs, rhs) <- pure b.val
         pure (PTransform (boundToFC fname b) n lhs rhs)

runElabDecl : OriginDesc -> IndentInfo -> Rule PDecl
runElabDecl fname indents
    = do tm <- bounds (pragma "runElab" *> expr pnowith fname indents)
         pure (PRunElabDecl (boundToFC fname tm) tm.val)

mutualDecls : OriginDesc -> IndentInfo -> Rule PDecl
mutualDecls fname indents
    = do ds <- bounds (decoratedKeyword fname "mutual" *> commit *> assert_total (nonEmptyBlock (topDecl fname)))
         pure (PMutual (boundToFC fname ds) (concat ds.val))

usingDecls : OriginDesc -> IndentInfo -> Rule PDecl
usingDecls fname indents
    = do b <- bounds (do decoratedKeyword fname "using"
                         commit
                         decoratedSymbol fname "("
                         us <- sepBy (decoratedSymbol fname ",")
                                     (do n <- optional
                                                (do x <- unqualifiedName
                                                    decoratedSymbol fname ":"
                                                    pure (UN x))
                                         ty <- typeExpr pdef fname indents
                                         pure (n, ty))
                         decoratedSymbol fname ")"
                         ds <- assert_total (nonEmptyBlock (topDecl fname))
                         pure (us, ds))
         (us, ds) <- pure b.val
         pure (PUsing (boundToFC fname b) us (collectDefs (concat ds)))

fnOpt : OriginDesc -> Rule PFnOpt
fnOpt fname
      = do x <- totalityOpt fname
           pure $ IFnOpt (Totality x)

fnDirectOpt : OriginDesc -> Rule PFnOpt
fnDirectOpt fname
    = do pragma "hint"
         pure $ IFnOpt (Hint True)
  <|> do pragma "globalhint"
         pure $ IFnOpt (GlobalHint False)
  <|> do pragma "defaulthint"
         pure $ IFnOpt (GlobalHint True)
  <|> do pragma "inline"
         commit
         pure $ IFnOpt Inline
  <|> do pragma "tcinline"
         commit
         pure $ IFnOpt TCInline
  <|> do pragma "extern"
         pure $ IFnOpt ExternFn
  <|> do pragma "macro"
         pure $ IFnOpt Macro
  <|> do pragma "spec"
         ns <- sepBy (decoratedSymbol fname ",") name
         pure $ IFnOpt (SpecArgs ns)
  <|> do pragma "foreign"
         cs <- block (expr pdef fname)
         pure $ PForeign cs

builtinDecl : OriginDesc -> IndentInfo -> Rule PDecl
builtinDecl fname indents
    = do b <- bounds (do pragma "builtin"
                         commit
                         t <- builtinType
                         n <- name
                         pure (t, n))
         (t, n) <- pure b.val
         pure $ PBuiltin (boundToFC fname b) t n

visOpt : OriginDesc -> Rule (Either Visibility PFnOpt)
visOpt fname
    = do vis <- visOption fname
         pure (Left vis)
  <|> do tot <- fnOpt fname
         pure (Right tot)
  <|> do opt <- fnDirectOpt fname
         pure (Right opt)

getVisibility : Maybe Visibility -> List (Either Visibility PFnOpt) ->
                EmptyRule Visibility
getVisibility Nothing [] = pure Private
getVisibility (Just vis) [] = pure vis
getVisibility Nothing (Left x :: xs) = getVisibility (Just x) xs
getVisibility (Just vis) (Left x :: xs)
   = fatalError "Multiple visibility modifiers"
getVisibility v (_ :: xs) = getVisibility v xs

recordConstructor : OriginDesc -> Rule Name
recordConstructor fname
  = do exactIdent "constructor"
       n <- mustWork $ decoratedDataConstructorName fname
       pure n

constraints : OriginDesc -> IndentInfo -> EmptyRule (List (Maybe Name, PTerm))
constraints fname indents
    = do tm <- appExpr pdef fname indents
         decoratedSymbol fname "=>"
         more <- constraints fname indents
         pure ((Nothing, tm) :: more)
  <|> do decoratedSymbol fname "("
         n <- decorate fname Bound name
         decoratedSymbol fname ":"
         tm <- expr pdef fname indents
         decoratedSymbol fname ")"
         decoratedSymbol fname "=>"
         more <- constraints fname indents
         pure ((Just n, tm) :: more)
  <|> pure []

implBinds : OriginDesc -> IndentInfo -> EmptyRule (List (Name, RigCount, PTerm))
implBinds fname indents
    = do decoratedSymbol fname "{"
         rig <- multiplicity fname
         n <- decorate fname Bound name
         decoratedSymbol fname ":"
         tm <- expr pdef fname indents
         decoratedSymbol fname "}"
         decoratedSymbol fname "->"
         more <- implBinds fname indents
         pure ((n, rig, tm) :: more)
  <|> pure []

ifaceParam : OriginDesc -> IndentInfo -> Rule (List Name, (RigCount, PTerm))
ifaceParam fname indents
    = do decoratedSymbol fname "("
         rig <- multiplicity fname
         ns <- sepBy1 (decoratedSymbol fname ",") (decorate fname Bound name)
         decoratedSymbol fname ":"
         tm <- expr pdef fname indents
         decoratedSymbol fname ")"
         pure (forget ns, (rig, tm))
  <|> do n <- bounds (decorate fname Bound name)
         pure ([n.val], (erased, PInfer (boundToFC fname n)))

ifaceDecl : OriginDesc -> IndentInfo -> Rule PDecl
ifaceDecl fname indents
    = do b <- bounds (do doc   <- option "" documentation
                         vis   <- visibility fname
                         col   <- column
                         decoratedKeyword fname "interface"
                         commit
                         cons   <- constraints fname indents
                         n      <- decorate fname Typ name
                         paramss <- many (ifaceParam fname indents)
                         let params = concatMap (\ (ns, rt) => map (\ n => (n, rt)) ns) paramss
                         det    <- option [] $ decoratedSymbol fname "|" *> sepBy (decoratedSymbol fname ",") (decorate fname Bound name)
                         decoratedKeyword fname "where"
                         dc <- optional (recordConstructor fname)
                         body <- assert_total (blockAfter col (topDecl fname))
                         pure (\fc : FC => PInterface fc
                                      vis cons n doc params det dc (collectDefs (concat body))))
         pure (b.val (boundToFC fname b))

implDecl : OriginDesc -> IndentInfo -> Rule PDecl
implDecl fname indents
    = do b <- bounds (do doc     <- option "" documentation
                         visOpts <- many (visOpt fname)
                         vis     <- getVisibility Nothing visOpts
                         let opts = mapMaybe getRight visOpts
                         col <- column
                         option () (decoratedKeyword fname "implementation")
                         iname  <- optional $ decoratedSymbol fname "["
                                           *> decorate fname Function name
                                           <* decoratedSymbol fname "]"
                         impls  <- implBinds fname indents
                         cons   <- constraints fname indents
                         n      <- decorate fname Typ name
                         params <- many (simpleExpr fname indents)
                         nusing <- option [] $ decoratedKeyword fname "using"
                                            *> forget <$> some (decorate fname Function name)
                         body <- optional $ decoratedKeyword fname "where" *> blockAfter col (topDecl fname)
                         pure $ \fc : FC =>
                            (PImplementation fc vis opts Single impls cons n params iname nusing
                                             (map (collectDefs . concat) body)))
         atEnd indents
         pure (b.val (boundToFC fname b))

fieldDecl : OriginDesc -> IndentInfo -> Rule (List PField)
fieldDecl fname indents
      = do doc <- option "" documentation
           decoratedSymbol fname "{"
           commit
           impl <- option Implicit (AutoImplicit <$ decoratedKeyword fname "auto")
           fs <- fieldBody doc impl
           decoratedSymbol fname "}"
           atEnd indents
           pure fs
    <|> do doc <- option "" documentation
           fs <- fieldBody doc Explicit
           atEnd indents
           pure fs
  where
    fieldBody : String -> PiInfo PTerm -> Rule (List PField)
    fieldBody doc p
        = do b <- bounds (do rig <- multiplicity fname
                             ns <- sepBy1 (decoratedSymbol fname ",") (do
                                     n <- decorate fname Function name
                                     pure n)
                             decoratedSymbol fname ":"
                             ty <- expr pdef fname indents
                             pure (\fc : FC => map (\n => MkField fc doc rig p n ty) (forget ns)))
             pure (b.val (boundToFC fname b))

typedArg : OriginDesc -> IndentInfo -> Rule (List (Name, RigCount, PiInfo PTerm, PTerm))
typedArg fname indents
    = do decoratedSymbol fname "("
         params <- pibindListName fname indents
         decoratedSymbol fname ")"
         pure $ map (\(c, n, tm) => (n.val, c, Explicit, tm)) params
  <|> do decoratedSymbol fname "{"
         commit
         info <-
                 (pure  AutoImplicit <* decoratedKeyword fname "auto"
              <|> (decoratedKeyword fname "default" *> DefImplicit <$> simpleExpr fname indents)
              <|> pure      Implicit)
         params <- pibindListName fname indents
         decoratedSymbol fname "}"
         pure $ map (\(c, n, tm) => (n.val, c, info, tm)) params

recordParam : OriginDesc -> IndentInfo -> Rule (List (Name, RigCount, PiInfo PTerm,  PTerm))
recordParam fname indents
    = typedArg fname indents
  <|> do n <- bounds name
         pure [(n.val, top, Explicit, PInfer (boundToFC fname n))]

recordDecl : OriginDesc -> IndentInfo -> Rule PDecl
recordDecl fname indents
    = do b <- bounds (do doc   <- option "" documentation
                         vis   <- visibility fname
                         col   <- column
                         decoratedKeyword fname "record"
                         n       <- mustWork (decoratedDataTypeName fname)
                         paramss <- many (recordParam fname indents)
                         let params = concat paramss
                         decoratedKeyword fname "where"
                         dcflds <- blockWithOptHeaderAfter col
                                      (\ idt => recordConstructor fname <* atEnd idt)
                                      (fieldDecl fname)
                         pure (\fc : FC => PRecord fc doc vis n params (fst dcflds) (concat (snd dcflds))))
         pure (b.val (boundToFC fname b))

paramDecls : OriginDesc -> IndentInfo -> Rule PDecl
paramDecls fname indents
    = do b1 <- bounds (decoratedKeyword fname "parameters")
         commit
         args <- bounds (newParamDecls fname indents <|> oldParamDecls fname indents)
         commit
         declarations <- the (Rule (WithBounds (List1 (List PDecl)))) (assert_total (Core.bounds $ nonEmptyBlock (topDecl fname)))
         mergedBounds <- pure $  b1 `mergeBounds` (args `mergeBounds` declarations)
         pure (PParameters (boundToFC fname mergedBounds) args.val (collectDefs (concat declarations.val)))

  where
    oldParamDecls : OriginDesc -> IndentInfo -> Rule (List (Name, RigCount, PiInfo PTerm, PTerm))
    oldParamDecls fname indents
        = do decoratedSymbol fname "("
             ps <- sepBy (decoratedSymbol fname ",")
                         (do x <- decoratedSimpleBinderName fname
                             decoratedSymbol fname ":"
                             ty <- typeExpr pdef fname indents
                             pure (UN x, top, Explicit, ty))
             decoratedSymbol fname ")"
             pure ps

    newParamDecls : OriginDesc -> IndentInfo -> Rule (List (Name, RigCount, PiInfo PTerm, PTerm))
    newParamDecls fname indents
        = map concat (some $ typedArg fname indents)


claims : OriginDesc -> IndentInfo -> Rule (List1 PDecl)
claims fname indents
    = do bs <- bounds (do
                  doc     <- option "" documentation
                  visOpts <- many (visOpt fname)
                  vis     <- getVisibility Nothing visOpts
                  let opts = mapMaybe getRight visOpts
                  rig  <- multiplicity fname
                  cls  <- tyDecls (decorate fname Function name)
                                  doc fname indents
                  pure $ map (\cl => the (Pair _ _) (doc, vis, opts, rig, cl)) cls)
         pure $ map (\(doc, vis, opts, rig, cl) : Pair _ _ =>
                           PClaim (boundToFC fname bs) rig vis opts cl)
                    bs.val

definition : OriginDesc -> IndentInfo -> Rule PDecl
definition fname indents
    = do nd <- bounds (clause 0 fname indents)
         pure (PDef (boundToFC fname nd) [nd.val])

fixDecl : OriginDesc -> IndentInfo -> Rule (List PDecl)
fixDecl fname indents
    = do b <- bounds (do fixity <- decorate fname Keyword $ fix
                         commit
                         prec <- decorate fname Keyword $ intLit
                         ops <- sepBy1 (decoratedSymbol fname ",") iOperator
                         pure (fixity, prec, ops))
         (fixity, prec, ops) <- pure b.val
         pure (map (PFixity (boundToFC fname b) fixity (fromInteger prec)) (forget ops))

directiveDecl : OriginDesc -> IndentInfo -> Rule PDecl
directiveDecl fname indents
    = do b <- bounds ((do d <- directive fname indents
                          pure (\fc : FC => PDirective fc d))
                     <|>
                      (do pragma "runElab"
                          tm <- expr pdef fname indents
                          atEnd indents
                          pure (\fc : FC => PReflect fc tm)))
         pure (b.val (boundToFC fname b))

-- Declared at the top
-- topDecl : OriginDesc -> IndentInfo -> Rule (List PDecl)
topDecl fname indents
    = do d <- dataDecl fname indents
         pure [d]
  <|> do ds <- claims fname indents
         pure (forget ds)
  <|> do d <- definition fname indents
         pure [d]
  <|> fixDecl fname indents
  <|> do d <- ifaceDecl fname indents
         pure [d]
  <|> do d <- implDecl fname indents
         pure [d]
  <|> do d <- recordDecl fname indents
         pure [d]
  <|> do d <- namespaceDecl fname indents
         pure [d]
  <|> do d <- mutualDecls fname indents
         pure [d]
  <|> do d <- paramDecls fname indents
         pure [d]
  <|> do d <- usingDecls fname indents
         pure [d]
  <|> do d <- builtinDecl fname indents
         pure [d]
  <|> do d <- runElabDecl fname indents
         pure [d]
  <|> do d <- transformDecl fname indents
         pure [d]
  <|> do d <- directiveDecl fname indents
         pure [d]
  <|> do dstr <- bounds (terminal "Expected CG directive"
                          (\case
                             CGDirective d => Just d
                             _ => Nothing))
         pure [let cgrest = span isAlphaNum dstr.val in
                   PDirective (boundToFC fname dstr)
                        (CGAction (fst cgrest) (stripBraces (trim (snd cgrest))))]
  <|> fatalError "Couldn't parse declaration"

-- All the clauses get parsed as one-clause definitions. Collect any
-- neighbouring clauses into one definition. This might mean merging two
-- functions which are different, if there are forward declarations,
-- but we'll split them in Desugar.idr. We can't do this now, because we
-- haven't resolved operator precedences yet.
-- Declared at the top.
-- collectDefs : List PDecl -> List PDecl
collectDefs [] = []
collectDefs (PDef annot cs :: ds)
    = let (csWithFC, rest) = spanBy isPDef ds
          cs' = cs ++ concat (map snd csWithFC)
          annot' = foldr
                   (\fc1, fc2 => fromMaybe EmptyFC (mergeFC fc1 fc2))
                   annot
                   (map fst csWithFC)
      in
          PDef annot' cs' :: assert_total (collectDefs rest)
collectDefs (PNamespace annot ns nds :: ds)
    = PNamespace annot ns (collectDefs nds) :: collectDefs ds
collectDefs (PMutual annot nds :: ds)
    = PMutual annot (collectDefs nds) :: collectDefs ds
collectDefs (d :: ds)
    = d :: collectDefs ds

export
import_ : OriginDesc -> IndentInfo -> Rule Import
import_ fname indents
    = do b <- bounds (do decoratedKeyword fname "import"
                         reexp <- option False (decoratedKeyword fname "public" $> True)
                         ns <- mustWork moduleIdent
                         nsAs <- option (miAsNamespace ns)
                                        (do exactIdent "as"
                                            mustWork namespaceId)
                         pure (reexp, ns, nsAs))
         atEnd indents
         (reexp, ns, nsAs) <- pure b.val
         pure (MkImport (boundToFC fname b) reexp ns nsAs)

export
prog : OriginDesc -> EmptyRule Module
prog fname
    = do b <- bounds (do doc    <- option "" documentation
                         nspace <- option (nsAsModuleIdent mainNS)
                                     (do decoratedKeyword fname "module"
                                         mustWork moduleIdent)
                         imports <- block (import_ fname)
                         pure (doc, nspace, imports))
         ds      <- block (topDecl fname)
         (doc, nspace, imports) <- pure b.val
         pure (MkModule (boundToFC fname b)
                        nspace imports doc (collectDefs (concat ds)))

export
progHdr : OriginDesc -> EmptyRule Module
progHdr fname
    = do b <- bounds (do doc    <- option "" documentation
                         nspace <- option (nsAsModuleIdent mainNS)
                                     (do decoratedKeyword fname "module"
                                         mustWork moduleIdent)
                         imports <- block (import_ fname)
                         pure (doc, nspace, imports))
         (doc, nspace, imports) <- pure b.val
         pure (MkModule (boundToFC fname b)
                        nspace imports doc [])

parseMode : Rule REPLEval
parseMode
     = do exactIdent "typecheck"
          pure EvalTC
   <|> do exactIdent "tc"
          pure EvalTC
   <|> do exactIdent "normalise"
          pure NormaliseAll
   <|> do exactIdent "normalize" -- oh alright then
          pure NormaliseAll
   <|> do exactIdent "execute"
          pure Execute
   <|> do exactIdent "exec"
          pure Execute

setVarOption : Rule REPLOpt
setVarOption
    = do exactIdent "eval"
         mode <- parseMode
         pure (EvalMode mode)
  <|> do exactIdent "editor"
         e <- unqualifiedName
         pure (Editor e)
  <|> do exactIdent "cg"
         c <- unqualifiedName
         pure (CG c)

setOption : Bool -> Rule REPLOpt
setOption set
    = do exactIdent "showimplicits"
         pure (ShowImplicits set)
  <|> do exactIdent "shownamespace"
         pure (ShowNamespace set)
  <|> do exactIdent "showtypes"
         pure (ShowTypes set)
  <|> do exactIdent "profile"
         pure (Profile set)
  <|> if set then setVarOption else fatalError "Unrecognised option"

replCmd : List String -> Rule ()
replCmd [] = fail "Unrecognised command"
replCmd (c :: cs)
    = exactIdent c
  <|> symbol c
  <|> replCmd cs

export
editCmd : Rule EditCmd
editCmd
    = do replCmd ["typeat"]
         line <- intLit
         col <- intLit
         n <- name
         pure (TypeAt (fromInteger line) (fromInteger col) n)
  <|> do replCmd ["cs"]
         upd <- option False (symbol "!" $> True)
         line <- intLit
         col <- intLit
         n <- name
         pure (CaseSplit upd (fromInteger line) (fromInteger col) n)
  <|> do replCmd ["ac"]
         upd <- option False (symbol "!" $> True)
         line <- intLit
         n <- name
         pure (AddClause upd (fromInteger line) n)
  <|> do replCmd ["ps", "proofsearch"]
         upd <- option False (symbol "!" $> True)
         line <- intLit
         n <- name
         pure (ExprSearch upd (fromInteger line) n [])
  <|> do replCmd ["psnext"]
         pure ExprSearchNext
  <|> do replCmd ["gd"]
         upd <- option False (symbol "!" $> True)
         line <- intLit
         n <- name
         nreject <- option 0 intLit
         pure (GenerateDef upd (fromInteger line) n (fromInteger nreject))
  <|> do replCmd ["gdnext"]
         pure GenerateDefNext
  <|> do replCmd ["ml", "makelemma"]
         upd <- option False (symbol "!" $> True)
         line <- intLit
         n <- name
         pure (MakeLemma upd (fromInteger line) n)
  <|> do replCmd ["mc", "makecase"]
         upd <- option False (symbol "!" $> True)
         line <- intLit
         n <- name
         pure (MakeCase upd (fromInteger line) n)
  <|> do replCmd ["mw", "makewith"]
         upd <- option False (symbol "!" $> True)
         line <- intLit
         n <- name
         pure (MakeWith upd (fromInteger line) n)
  <|> fatalError "Unrecognised command"

export
data CmdArg : Type where
     ||| The command takes no arguments.
     NoArg : CmdArg

     ||| The command takes a name.
     NameArg : CmdArg

     ||| The command takes an expression.
     ExprArg : CmdArg

     ||| The command takes a list of declarations
     DeclsArg : CmdArg

     ||| The command takes a number.
     NumberArg : CmdArg

     ||| The command takes a number or auto.
     AutoNumberArg : CmdArg

     ||| The command takes an option.
     OptionArg : CmdArg

     ||| The command takes a file.
     FileArg : CmdArg

     ||| The command takes a module.
     ModuleArg : CmdArg

     ||| The command takes a string
     StringArg : CmdArg

     ||| The command takes a on or off.
     OnOffArg : CmdArg

     ||| The command takes multiple arguments.
     Args : List CmdArg -> CmdArg

export
Show CmdArg where
  show NoArg = ""
  show NameArg = "<name>"
  show ExprArg = "<expr>"
  show DeclsArg = "<decls>"
  show NumberArg = "<number>"
  show AutoNumberArg = "<number|auto>"
  show OptionArg = "<option>"
  show FileArg = "<file>"
  show ModuleArg = "<module>"
  show StringArg = "<string>"
  show OnOffArg = "(on|off)"
  show (Args args) = showSep " " (map show args)

export
data ParseCmd : Type where
     ParseREPLCmd : List String -> ParseCmd
     ParseKeywordCmd : String -> ParseCmd
     ParseIdentCmd : String -> ParseCmd

CommandDefinition : Type
CommandDefinition = (List String, CmdArg, String, Rule REPLCmd)

CommandTable : Type
CommandTable = List CommandDefinition

extractNames : ParseCmd -> List String
extractNames (ParseREPLCmd names) = names
extractNames (ParseKeywordCmd keyword) = [keyword]
extractNames (ParseIdentCmd ident) = [ident]

runParseCmd : ParseCmd -> Rule ()
runParseCmd (ParseREPLCmd names) = replCmd names
runParseCmd (ParseKeywordCmd keyword') = keyword keyword'
runParseCmd (ParseIdentCmd ident) = exactIdent ident

noArgCmd : ParseCmd -> REPLCmd -> String -> CommandDefinition
noArgCmd parseCmd command doc = (names, NoArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      pure command

nameArgCmd : ParseCmd -> (Name -> REPLCmd) -> String -> CommandDefinition
nameArgCmd parseCmd command doc = (names, NameArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      n <- mustWork name
      pure (command n)

stringArgCmd : ParseCmd -> (String -> REPLCmd) -> String -> CommandDefinition
stringArgCmd parseCmd command doc = (names, StringArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      s <- mustWork simpleStr
      pure (command s)

moduleArgCmd : ParseCmd -> (ModuleIdent -> REPLCmd) -> String -> CommandDefinition
moduleArgCmd parseCmd command doc = (names, ModuleArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      n <- mustWork moduleIdent
      pure (command n)

exprArgCmd : ParseCmd -> (PTerm -> REPLCmd) -> String -> CommandDefinition
exprArgCmd parseCmd command doc = (names, ExprArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      tm <- mustWork $ expr pdef (Virtual Interactive) init
      pure (command tm)

declsArgCmd : ParseCmd -> (List PDecl -> REPLCmd) -> String -> CommandDefinition
declsArgCmd parseCmd command doc = (names, DeclsArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd
    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      tm <- mustWork $ topDecl (Virtual Interactive) init
      pure (command tm)

optArgCmd : ParseCmd -> (REPLOpt -> REPLCmd) -> Bool -> String -> CommandDefinition
optArgCmd parseCmd command set doc = (names, OptionArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      opt <- mustWork $ setOption set
      pure (command opt)

numberArgCmd : ParseCmd -> (Nat -> REPLCmd) -> String -> CommandDefinition
numberArgCmd parseCmd command doc = (names, NumberArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      i <- mustWork intLit
      pure (command (fromInteger i))

autoNumberArgCmd : ParseCmd -> (Maybe Nat -> REPLCmd) -> String -> CommandDefinition
autoNumberArgCmd parseCmd command doc = (names, AutoNumberArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    autoNumber : Rule (Maybe Nat)
    autoNumber = Nothing <$ keyword "auto"
             <|> Just . fromInteger <$> intLit

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      mi <- mustWork autoNumber
      pure (command mi)

onOffArgCmd : ParseCmd -> (Bool -> REPLCmd) -> String -> CommandDefinition
onOffArgCmd parseCmd command doc = (names, OnOffArg, doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      i <- mustWork onOffLit
      pure (command i)

compileArgsCmd : ParseCmd -> (PTerm -> String -> REPLCmd) -> String -> CommandDefinition
compileArgsCmd parseCmd command doc
    = (names, Args [FileArg, ExprArg], doc, parse)
  where
    names : List String
    names = extractNames parseCmd

    parse : Rule REPLCmd
    parse = do
      symbol ":"
      runParseCmd parseCmd
      n <- mustWork unqualifiedName
      tm <- mustWork $ expr pdef (Virtual Interactive) init
      pure (command tm n)

loggingArgCmd : ParseCmd -> (Maybe LogLevel -> REPLCmd) -> String -> CommandDefinition
loggingArgCmd parseCmd command doc = (names, Args [StringArg, NumberArg], doc, parse) where

  names : List String
  names = extractNames parseCmd

  parse : Rule REPLCmd
  parse = do
    symbol ":"
    runParseCmd parseCmd
    lvl <- mustWork logLevel
    pure (command lvl)

parserCommandsForHelp : CommandTable
parserCommandsForHelp =
  [ exprArgCmd (ParseREPLCmd ["t", "type"]) Check "Check the type of an expression"
  , exprArgCmd (ParseREPLCmd ["ti"]) CheckWithImplicits "Check the type of an expression, showing implicit arguments"
  , nameArgCmd (ParseREPLCmd ["printdef"]) PrintDef "Show the definition of a function"
  , exprArgCmd (ParseREPLCmd ["s", "search"]) TypeSearch "Search for values by type"
  , nameArgCmd (ParseIdentCmd "di") DebugInfo "Show debugging information for a name"
  , moduleArgCmd (ParseKeywordCmd "module") ImportMod "Import an extra module"
  , noArgCmd (ParseREPLCmd ["q", "quit", "exit"]) Quit "Exit the Idris system"
  , noArgCmd (ParseREPLCmd ["cwd"]) CWD "Displays the current working directory"
  , stringArgCmd (ParseREPLCmd ["cd"]) CD "Change the current working directory"
  , stringArgCmd (ParseREPLCmd ["sh"]) RunShellCommand "Run a shell command"
  , optArgCmd (ParseIdentCmd "set") SetOpt True "Set an option"
  , optArgCmd (ParseIdentCmd "unset") SetOpt False "Unset an option"
  , noArgCmd (ParseREPLCmd ["opts"]) GetOpts "Show current options settings"
  , compileArgsCmd (ParseREPLCmd ["c", "compile"]) Compile "Compile to an executable"
  , exprArgCmd (ParseIdentCmd "exec") Exec "Compile to an executable and run"
  , stringArgCmd (ParseIdentCmd "directive") CGDirective "Set a codegen-specific directive"
  , stringArgCmd (ParseREPLCmd ["l", "load"]) Load "Load a file"
  , noArgCmd (ParseREPLCmd ["r", "reload"]) Reload "Reload current file"
  , noArgCmd (ParseREPLCmd ["e", "edit"]) Edit "Edit current file using $EDITOR or $VISUAL"
  , nameArgCmd (ParseREPLCmd ["miss", "missing"]) Missing "Show missing clauses"
  , nameArgCmd (ParseKeywordCmd "total") Total "Check the totality of a name"
  , exprArgCmd (ParseIdentCmd "doc") Doc "Show documentation for a name or primitive"
  , moduleArgCmd (ParseIdentCmd "browse") (Browse . miAsNamespace) "Browse contents of a namespace"
  , loggingArgCmd (ParseREPLCmd ["log", "logging"]) SetLog "Set logging level"
  , autoNumberArgCmd (ParseREPLCmd ["consolewidth"]) SetConsoleWidth "Set the width of the console output (0 for unbounded) (auto by default)"
  , onOffArgCmd (ParseREPLCmd ["color", "colour"]) SetColor "Whether to use color for the console output (enabled by default)"
  , noArgCmd (ParseREPLCmd ["m", "metavars"]) Metavars "Show remaining proof obligations (metavariables or holes)"
  , noArgCmd (ParseREPLCmd ["version"]) ShowVersion "Display the Idris version"
  , noArgCmd (ParseREPLCmd ["?", "h", "help"]) Help "Display this help text"
  , declsArgCmd (ParseKeywordCmd "let") NewDefn "Define a new value"
  , stringArgCmd (ParseREPLCmd ["lp", "loadpackage"]) ImportPackage "Load all modules of the package"
  , exprArgCmd (ParseREPLCmd ["fs", "fsearch"]) FuzzyTypeSearch "Search for global definitions by sketching the names distribution of the wanted type(s)."
  ]

export
help : List (List String, CmdArg, String)
help = (["<expr>"], NoArg, "Evaluate an expression") ::
         map (\ (names, args, text, _) =>
               (map (":" ++) names, args, text)) parserCommandsForHelp

nonEmptyCommand : Rule REPLCmd
nonEmptyCommand =
  choice (map (\ (_, _, _, parser) => parser) parserCommandsForHelp)

eval : Rule REPLCmd
eval = do
  tm <- expr pdef (Virtual Interactive) init
  pure (Eval tm)

export
command : EmptyRule REPLCmd
command
    = eoi $> NOP
  <|> nonEmptyCommand
  <|> symbol ":?" $> Help -- special case, :? doesn't fit into above scheme
  <|> symbol ":" *> Editing <$> editCmd
  <|> eval
