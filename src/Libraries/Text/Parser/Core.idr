module Libraries.Text.Parser.Core

import Data.Bool
import Data.List
import Data.List1

import public Libraries.Control.Delayed
import public Libraries.Text.Bounded

%default total

-- TODO: Add some primitives for helping with error messages.
-- e.g. perhaps set a string to state what we're currently trying to
-- parse, or to say what the next expected token is in words

||| Description of a language's grammar. The `tok` parameter is the type
||| of tokens, and the `consumes` flag is True if the language is guaranteed
||| to be non-empty - that is, successfully parsing the language is guaranteed
||| to consume some input.
export
data Grammar : (state : Type) -> (tok : Type) -> (consumes : Bool) -> Type -> Type where
     Empty : (val : ty) -> Grammar state tok False ty
     Terminal : String -> (tok -> Maybe a) -> Grammar state tok True a
     NextIs : String -> (tok -> Bool) -> Grammar state tok False tok
     EOF : Grammar state tok False ()

     Fail : (location : Maybe Bounds) -> (fatal : Bool) -> String -> Grammar state tok c ty
     Try : Grammar state tok c ty -> Grammar state tok c ty

     Commit : Grammar state tok False ()
     MustWork : Grammar state tok c a -> Grammar state tok c a

     SeqEat : {c2 : Bool} ->
              Grammar state tok True a -> Inf (a -> Grammar state tok c2 b) ->
              Grammar state tok True b
     SeqEmpty : {c1, c2 : Bool} ->
                Grammar state tok c1 a -> (a -> Grammar state tok c2 b) ->
                Grammar state tok (c1 || c2) b

     ThenEat : {c2 : Bool} ->
               Grammar state tok True () -> Inf (Grammar state tok c2 a) ->
               Grammar state tok True a
     ThenEmpty : {c1, c2 : Bool} ->
                 Grammar state tok c1 () -> Grammar state tok c2 a ->
                 Grammar state tok (c1 || c2) a

     Alt : {c1, c2 : Bool} ->
           Grammar state tok c1 ty -> Lazy (Grammar state tok c2 ty) ->
           Grammar state tok (c1 && c2) ty
     Bounds : Grammar state tok c ty -> Grammar state tok c (WithBounds ty)
     Position : Grammar state tok False Bounds

     Act : state -> Grammar state tok False ()

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume some input. If the first one consumes input, the
||| second is allowed to be recursive (because it means some input has been
||| consumed and therefore the input is smaller)
export %inline
(>>=) : {c1, c2 : Bool} ->
        Grammar state tok c1 a ->
        inf c1 (a -> Grammar state tok c2 b) ->
        Grammar state tok (c1 || c2) b
(>>=) {c1 = False} = SeqEmpty
(>>=) {c1 = True}  = SeqEat

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume some input. If the first one consumes input, the
||| second is allowed to be recursive (because it means some input has been
||| consumed and therefore the input is smaller)
public export %inline %tcinline
(>>) : {c1, c2 : Bool} ->
        Grammar state tok c1 () ->
        inf c1 (Grammar state tok c2 a) ->
        Grammar state tok (c1 || c2) a
(>>) {c1 = False} = ThenEmpty
(>>) {c1 = True} = ThenEat

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume input. This is an explicitly non-infinite version
||| of `>>=`.
export %inline
seq : {c1,c2 : Bool} ->
      Grammar state tok c1 a ->
      (a -> Grammar state tok c2 b) ->
      Grammar state tok (c1 || c2) b
seq = SeqEmpty

||| Sequence a grammar followed by the grammar it returns.
export %inline
join : {c1,c2 : Bool} ->
       Grammar state tok c1 (Grammar state tok c2 a) ->
       Grammar state tok (c1 || c2) a
join {c1 = False} p = SeqEmpty p id
join {c1 = True} p = SeqEat p id

||| Allows the result of a grammar to be mapped to a different value.
export
{c : _} ->
Functor (Grammar state tok c) where
  map f (Empty val)  = Empty (f val)
  map f (Fail bd fatal msg) = Fail bd fatal msg
  map f (Try g) = Try (map f g)
  map f (MustWork g) = MustWork (map f g)
  map f (Terminal msg g) = Terminal msg (map f . g)
  map f (Alt x y)    = Alt (map f x) (map f y)
  map f (SeqEat act next)
      = SeqEat act (\val => map f (next val))
  map f (SeqEmpty act next)
      = SeqEmpty act (\ val => map f (next val))
  map f (ThenEat act next)
      = ThenEat act (map f next)
  map f (ThenEmpty act next)
      = ThenEmpty act (map f next)
  map {c} f (Bounds act)
    = rewrite sym $ orFalseNeutral c in
      SeqEmpty (Bounds act) (Empty . f) -- Bounds (map f act)
  -- The remaining constructors (NextIs, EOF, Commit) have a fixed type,
  -- so a sequence must be used.
  map {c = False} f p = SeqEmpty p (Empty . f)

||| Give two alternative grammars. If both consume, the combination is
||| guaranteed to consume.
export %inline
(<|>) : {c1,c2 : Bool} ->
        Grammar state tok c1 ty ->
        Lazy (Grammar state tok c2 ty) ->
        Grammar state tok (c1 && c2) ty
(<|>) = Alt

infixr 2 <||>
||| Take the tagged disjunction of two grammars. If both consume, the
||| combination is guaranteed to consume.
export
(<||>) : {c1,c2 : Bool} ->
        Grammar state tok c1 a ->
        Lazy (Grammar state tok c2 b) ->
        Grammar state tok (c1 && c2) (Either a b)
(<||>) p q = (Left <$> p) <|> (Right <$> q)

||| Sequence a grammar with value type `a -> b` and a grammar
||| with value type `a`. If both succeed, apply the function
||| from the first grammar to the value from the second grammar.
||| Guaranteed to consume if either grammar consumes.
export %inline
(<*>) : {c1, c2 : Bool} ->
        Grammar state tok c1 (a -> b) ->
        Grammar state tok c2 a ->
        Grammar state tok (c1 || c2) b
(<*>) x y = SeqEmpty x (\f => map f y)

||| Sequence two grammars. If both succeed, use the value of the first one.
||| Guaranteed to consume if either grammar consumes.
export %inline
(<*) : {c1,c2 : Bool} ->
       Grammar state tok c1 a ->
       Grammar state tok c2 b ->
       Grammar state tok (c1 || c2) a
(<*) x y = map const x <*> y

||| Sequence two grammars. If both succeed, use the value of the second one.
||| Guaranteed to consume if either grammar consumes.
export %inline
(*>) : {c1,c2 : Bool} ->
       Grammar state tok c1 a ->
       Grammar state tok c2 b ->
       Grammar state tok (c1 || c2) b
(*>) x y = map (const id) x <*> y

export %inline
act : state -> Grammar state tok False ()
act = Act

||| Produce a grammar that can parse a different type of token by providing a
||| function converting the new token type into the original one.
export
mapToken : (a -> b) -> Grammar state b c ty -> Grammar state a c ty
mapToken f (Empty val) = Empty val
mapToken f (Terminal msg g) = Terminal msg (g . f)
mapToken f (NextIs msg g) = SeqEmpty (NextIs msg (g . f)) (Empty . f)
mapToken f EOF = EOF
mapToken f (Fail bd fatal msg) = Fail bd fatal msg
mapToken f (Try g) = Try (mapToken f g)
mapToken f (MustWork g) = MustWork (mapToken f g)
mapToken f Commit = Commit
mapToken f (SeqEat act next)
  = SeqEat (mapToken f act) (\x => mapToken f (next x))
mapToken f (SeqEmpty act next)
  = SeqEmpty (mapToken f act) (\x => mapToken f (next x))
mapToken f (ThenEat act next)
  = ThenEat (mapToken f act) (mapToken f next)
mapToken f (ThenEmpty act next)
  = ThenEmpty (mapToken f act) (mapToken f next)
mapToken f (Alt x y) = Alt (mapToken f x) (mapToken f y)
mapToken f (Bounds act) = Bounds (mapToken f act)
mapToken f Position = Position
mapToken f (Act action) = Act action

||| Always succeed with the given value.
export %inline
pure : (val : ty) -> Grammar state tok False ty
pure = Empty

||| Check whether the next token satisfies a predicate
export %inline
nextIs : String -> (tok -> Bool) -> Grammar state tok False tok
nextIs = NextIs

||| Look at the next token in the input
export %inline
peek : Grammar state tok False tok
peek = nextIs "Unrecognised token" (const True)

||| Succeeds if running the predicate on the next token returns Just x,
||| returning x. Otherwise fails.
export %inline
terminal : String -> (tok -> Maybe a) -> Grammar state tok True a
terminal = Terminal

||| Always fail with a message
export %inline
fail : String -> Grammar state tok c ty
fail = Fail Nothing False

||| Always fail with a message and a location
export %inline
failLoc : Bounds -> String -> Grammar state tok c ty
failLoc b = Fail (Just b) False

||| Fail with no possibility for recovery (i.e.
||| no alternative parsing can succeed).
export %inline
fatalError : String -> Grammar state tok c ty
fatalError = Fail Nothing True

||| Fail with no possibility for recovery (i.e.
||| no alternative parsing can succeed).
export %inline
fatalLoc : Bounds -> String -> Grammar state tok c ty
fatalLoc b = Fail (Just b) True

||| Catch a fatal error
export %inline
try : Grammar state tok c ty -> Grammar state tok c ty
try = Try

||| Succeed if the input is empty
export %inline
eof : Grammar state tok False ()
eof = EOF

||| Commit to an alternative; if the current branch of an alternative
||| fails to parse, no more branches will be tried
export %inline
commit : Grammar state tok False ()
commit = Commit

||| If the parser fails, treat it as a fatal error
export %inline
mustWork : {c : Bool} -> Grammar state tok c ty -> Grammar state tok c ty
mustWork = MustWork

||| If the parser fails, treat it as a fatal error and explain why
export
mustWorkBecause :
  {c : Bool} -> Bounds -> String ->
  Grammar state tok c ty -> Grammar state tok c ty
mustWorkBecause {c} loc msg p
  = rewrite sym (andSameNeutral c) in
    p <|> fatalLoc loc msg
export %inline
bounds : Grammar state tok c ty -> Grammar state tok c (WithBounds ty)
bounds = Bounds

export %inline
position : Grammar state tok False Bounds
position = Position

public export
data ParsingError tok = Error String (Maybe Bounds)

data ParseResult : Type -> Type -> Type -> Type where
     Failure : (committed : Bool) -> (fatal : Bool) ->
               List1 (ParsingError tok) -> ParseResult state tok ty
     Res : state -> (committed : Bool) ->
           (val : WithBounds ty) -> (more : List (WithBounds tok)) -> ParseResult state tok ty

mergeWith : WithBounds ty -> ParseResult state tok sy -> ParseResult state tok sy
mergeWith x (Res s committed val more) = Res s committed (mergeBounds x val) more
mergeWith x v = v

doParse : Semigroup state => state -> (commit : Bool) ->
          (act : Grammar state tok c ty) ->
          (xs : List (WithBounds tok)) ->
          ParseResult state tok ty
doParse s com (Empty val) xs = Res s com (irrelevantBounds val) xs
doParse s com (Fail location fatal str) xs
    = Failure com fatal (Error str (location <|> (bounds <$> head' xs)) ::: Nil)
doParse s com (Try g) xs = case doParse s com g xs of
  -- recover from fatal match but still propagate the 'commit'
  Failure com _ errs => Failure com False errs
  res => res
doParse s com Commit xs = Res s True (irrelevantBounds ()) xs
doParse s com (MustWork g) xs =
  case assert_total (doParse s com g xs) of
       Failure com' _ errs => Failure com' True errs
       res => res
doParse s com (Terminal err f) [] = Failure com False (Error "End of input" Nothing ::: Nil)
doParse s com (Terminal err f) (x :: xs) =
  case f x.val of
       Nothing => Failure com False (Error err (Just x.bounds) ::: Nil)
       Just a => Res s com (const a <$> x) xs
doParse s com EOF [] = Res s com (irrelevantBounds ()) []
doParse s com EOF (x :: xs) = Failure com False (Error "Expected end of input" (Just x.bounds) ::: Nil)
doParse s com (NextIs err f) [] = Failure com False (Error "End of input" Nothing ::: Nil)
doParse s com (NextIs err f) (x :: xs)
      = if f x.val
           then Res s com (removeIrrelevance x) (x :: xs)
           else Failure com False (Error err (Just x.bounds) ::: Nil)
doParse s com (Alt {c1} {c2} x y) xs
    = case doParse s False x xs of
           Failure com' fatal errs
              => if com' || fatal
                        -- If the alternative had committed, don't try the
                        -- other branch (and reset commit flag)
                   then Failure com fatal errs
                   else case (assert_total doParse s False y xs) of
                             (Failure com'' fatal' errs') => if com'' || fatal'
                                                                     -- Only add the errors together if the second branch
                                                                     -- is also non-committed and non-fatal.
                                                             then Failure com'' fatal' errs'
                                                             else Failure False False (errs ++ errs')
                             (Res s _ val xs) => Res s com val xs
           -- Successfully parsed the first option, so use the outer commit flag
           Res s _ val xs => Res s com val xs
doParse s com (SeqEmpty act next) xs
    = case assert_total (doParse s com act xs) of
           Failure com fatal errs => Failure com fatal errs
           Res s com v xs =>
             mergeWith v (assert_total $ doParse s com (next v.val) xs)
doParse s com (SeqEat act next) xs
    = case assert_total (doParse s com act xs) of
           Failure com fatal errs => Failure com fatal errs
           Res s com v xs =>
             mergeWith v (assert_total $ doParse s com (next v.val) xs)
doParse s com (ThenEmpty act next) xs
    = case assert_total (doParse s com act xs) of
           Failure com fatal errs => Failure com fatal errs
           Res s com v xs =>
             mergeWith v (assert_total $ doParse s com next xs)
doParse s com (ThenEat act next) xs
    = case assert_total (doParse s com act xs) of
           Failure com fatal errs => Failure com fatal errs
           Res s com v xs =>
             mergeWith v (assert_total $ doParse s com next xs)
doParse s com (Bounds act) xs
    = case assert_total (doParse s com act xs) of
           Failure com fatal errs => Failure com fatal errs
           Res s com v xs => Res s com (const v <$> v) xs
doParse s com Position [] = Failure com False (Error "End of input" Nothing ::: Nil)
doParse s com Position (x :: xs)
    = Res s com (irrelevantBounds x.bounds) (x :: xs)
doParse s com (Act action) xs = Res (s <+> action) com (irrelevantBounds ()) xs

||| Parse a list of tokens according to the given grammar. If successful,
||| returns a pair of the parse result and the unparsed tokens (the remaining
||| input).
export
parse : {c : Bool} -> (act : Grammar () tok c ty) -> (xs : List (WithBounds tok)) ->
        Either (List1 (ParsingError tok)) (ty, List (WithBounds tok))
parse act xs
    = case doParse neutral False act xs of
           Failure _ _ errs => Left errs
           Res _ _ v rest => Right (v.val, rest)

export
parseWith : Monoid state => {c : Bool} -> (act : Grammar state tok c ty) -> (xs : List (WithBounds tok)) ->
        Either (List1 (ParsingError tok)) (state, ty, List (WithBounds tok))
parseWith act xs
    = case doParse neutral False act xs of
           Failure _ _ errs => Left errs
           Res s _ v rest => Right (s, v.val, rest)
