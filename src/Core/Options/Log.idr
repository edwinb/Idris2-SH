module Core.Options.Log

import public Data.List
import Data.List1
import public Data.Maybe
import Libraries.Data.StringMap
import Libraries.Data.StringTrie
import Data.String
import Data.These
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util
import Libraries.Text.PrettyPrint.Prettyprinter.Render.String

%default total

||| Log levels are characterised by two things:
||| * a dot-separated path of ever finer topics of interest e.g. scope.let
||| * a natural number corresponding to the verbosity level e.g. 5
|||
||| If the user asks for some logs by writing
|||
|||     %log scope 5
|||
||| they will get all of the logs whose path starts with `scope` and whose
||| verbosity level is less or equal to `5`. By combining different logging
||| directives, users can request information about everything (with a low
||| level of details) and at the same time focus on a particular subsystem
||| they want to get a lot of information about. For instance:
|||
|||     %log 1
|||     %log scope.let 10
|||
||| will deliver basic information about the various phases the compiler goes
||| through and deliver a lot of information about scope-checking let binders.

----------------------------------------------------------------------------------
-- INDIVIDUAL LOG LEVEL

public export
knownTopics : List (String, Maybe String)
knownTopics = [
    ("auto", Nothing),
    ("builtin.Natural", Nothing),
    ("builtin.Natural.addTransform", Nothing),
    ("builtin.NaturalToInteger", Nothing),
    ("builtin.NaturalToInteger.addTransforms", Nothing),
    ("builtin.IntegerToNatural", Nothing),
    ("builtin.IntegerToNatural.addTransforms", Nothing),
    ("compile.casetree", Nothing),
    ("compile.casetree.clauses", Nothing),
    ("compile.casetree.getpmdef", Nothing),
    ("compile.casetree.intermediate", Nothing),
    ("compile.casetree.pick", Nothing),
    ("compile.casetree.partition", Nothing),
    ("compiler.inline.eval", Nothing),
    ("compiler.interpreter", Nothing),
    ("compiler.refc", Nothing),
    ("compiler.refc.cc", Nothing),
    ("compiler.scheme.chez", Nothing),
    ("coverage", Nothing),
    ("coverage.empty", Nothing),
    ("coverage.missing", Nothing),
    ("coverage.recover", Nothing),
    ("declare.data", Nothing),
    ("declare.data.constructor", Nothing),
    ("declare.data.parameters", Nothing),
    ("declare.def", Nothing),
    ("declare.def.clause", Nothing),
    ("declare.def.clause.impossible", Nothing),
    ("declare.def.clause.with", Nothing),
    ("declare.def.impossible", Nothing),
    ("declare.def.lhs", Nothing),
    ("declare.def.lhs.implicits", Nothing),
    ("declare.param", Nothing),
    ("declare.record", Nothing),
    ("declare.record.field", Nothing),
    ("declare.record.projection", Nothing),
    ("declare.record.projection.prefix", Nothing),
    ("declare.type", Nothing),
    ("desugar.idiom", Nothing),
    ("doc.record", Nothing),
    ("elab", Nothing),
    ("elab.ambiguous", Nothing),
    ("elab.app.var", Nothing),
    ("elab.app.lhs", Nothing),
    ("elab.as", Nothing),
    ("elab.bindnames", Nothing),
    ("elab.binder", Nothing),
    ("elab.case", Nothing),
    ("elab.def.local", Nothing),
    ("elab.delay", Nothing),
    ("elab.hole", Nothing),
    ("elab.implicits", Nothing),
    ("elab.implementation", Nothing),
    ("elab.interface", Nothing),
    ("elab.interface.default", Nothing),
    ("elab.local", Nothing),
    ("elab.prune", Nothing),
    ("elab.record", Nothing),
    ("elab.retry", Nothing),
    ("elab.rewrite", Nothing),
    ("elab.unify", Nothing),
    ("elab.update", Nothing),
    ("elab.with", Nothing),
    ("eval.casetree", Nothing),
    ("eval.casetree.stuck", Nothing),
    ("eval.eta", Nothing),
    ("eval.stuck", Nothing),
    ("idemode.hole", Nothing),
    ("ide-mode.highlight", Nothing),
    ("ide-mode.highlight.alias", Nothing),
    ("ide-mode.send", Nothing),
    ("import", Nothing),
    ("import.file", Nothing),
    ("interaction.casesplit", Nothing),
    ("interaction.generate", Nothing),
    ("interaction.search", Nothing),
    ("metadata.names", Nothing),
    ("module.hash", Nothing),
    ("pattern", Nothing),
    ("pattern.implicit", Nothing),
    ("quantity", Nothing),
    ("quantity.hole", Nothing),
    ("quantity.hole.update", Nothing),
    ("repl.eval", Nothing),
    ("resugar.var", Nothing),
    ("specialise", Nothing),
    ("totality", Nothing),
    ("totality.positivity", Nothing),
    ("totality.termination", Nothing),
    ("totality.termination.calc", Nothing),
    ("totality.termination.guarded", Nothing),
    ("totality.termination.sizechange", Nothing),
    ("totality.termination.sizechange.checkCall", Nothing),
    ("totality.termination.sizechange.checkCall.inPath", Nothing),
    ("totality.termination.sizechange.checkCall.inPathNot.restart", Nothing),
    ("totality.termination.sizechange.checkCall.inPathNot.return", Nothing),
    ("totality.termination.sizechange.inPath", Nothing),
    ("totality.termination.sizechange.isTerminating", Nothing),
    ("totality.termination.sizechange.needsChecking", Nothing),
    ("transform.lhs", Nothing),
    ("transform.rhs", Nothing),
    ("ttc.read", Nothing),
    ("ttc.write", Nothing),
    ("typesearch.equiv", Nothing),
    ("unelab.case", Nothing),
    ("unelab.var", Nothing),
    ("unify", Nothing),
    ("unify.application", Nothing),
    ("unify.binder", Nothing),
    ("unify.constant", Nothing),
    ("unify.constraint", Nothing),
    ("unify.delay", Nothing),
    ("unify.equal", Nothing),
    ("unify.head", Nothing),
    ("unify.hole", Nothing),
    ("unify.instantiate", Nothing),
    ("unify.invertible", Nothing),
    ("unify.meta", Nothing),
    ("unify.noeta", Nothing),
    ("unify.postpone", Nothing),
    ("unify.retry", Nothing),
    ("unify.search", Nothing),
    ("unify.unsolved", Nothing)
]

export
helpTopics : String
helpTopics = show $ vcat $ map helpTopic knownTopics

  where

  helpTopic : (String, Maybe String) -> Doc ()
  helpTopic (str, mblurb)
    = let title = "+" <++> pretty str
          blurb = maybe [] ((::[]) . indent 2 . reflow) mblurb
      in vcat (title :: blurb)

public export
KnownTopic : String -> Type
KnownTopic s = IsJust (lookup s knownTopics)

||| An individual log level is a pair of a list of non-empty strings and a number.
||| We keep the representation opaque to force users to call the smart constructor
export
data LogLevel : Type where
  MkLogLevel : List String -> Nat -> LogLevel

||| If we have already processed the input string into (maybe) a non-empty list of
||| non-empty topics we can safely make a `LogLevel`.
export
mkLogLevel' : Maybe (List1 String) -> Nat -> LogLevel
mkLogLevel' ps n = MkLogLevel (maybe [] forget ps) n

||| The smart constructor makes sure that the empty string is mapped to the empty
||| list. This bypasses the fact that the function `split` returns a non-empty
||| list no matter what.
|||
||| However, invoking this function comes without guarantees that
||| the passed string corresponds to a known topic. For this,
||| use `mkLogLevel`.
|||
||| Use this function to create user defined loglevels, for instance, during
||| elaborator reflection.
export
mkUnverifiedLogLevel : (s : String) -> Nat -> LogLevel
mkUnverifiedLogLevel "" = mkLogLevel' Nothing
mkUnverifiedLogLevel ps = mkLogLevel' (Just (split (== '.') ps))

||| Like `mkUnverifiedLogLevel` but with a compile time check that
||| the passed string is a known topic.
export
mkLogLevel : (s : String) -> {auto 0 _ : KnownTopic s} -> Nat -> LogLevel
mkLogLevel s = mkUnverifiedLogLevel s

||| The unsafe constructor should only be used in places where the topic has already
||| been appropriately processed.
export
unsafeMkLogLevel : List String -> Nat -> LogLevel
unsafeMkLogLevel = MkLogLevel

||| The topics attached to a `LogLevel` can be reconstructed from the list of strings.
export
topics : LogLevel -> List String
topics (MkLogLevel ps _) = ps

||| The verbosity is provided by the natural number
export
verbosity : LogLevel -> Nat
verbosity (MkLogLevel _ n) = n

||| When writing generic functions we sometimes want to keep the same topic but
||| change the verbosity.
export
withVerbosity : Nat -> LogLevel -> LogLevel
withVerbosity n (MkLogLevel ps _) = MkLogLevel ps n

||| A log level is show as `P.Q.R:N` where `P`, `Q` and `R` are topics and `N` is
||| a verbosity level. If there are no topics then we simply print `N`.
export
Show LogLevel where

  show (MkLogLevel ps n) = case ps of
    [] => show n
    _  => fastAppend (intersperse "." ps) ++ ":" ++ show n

export
Pretty LogLevel where

  pretty = pretty . show

export
parseLogLevel : String -> Maybe LogLevel
parseLogLevel str = do
  (c, n) <- let nns = split (== ':') str
                n = head nns
                ns = tail nns in
                case ns of
                     [] => pure (MkLogLevel [], n)
                     [ns] => pure (mkUnverifiedLogLevel n, ns)
                     _ => Nothing
  lvl <- parsePositive n
  pure $ c (fromInteger lvl)

----------------------------------------------------------------------------------
-- COLLECTION OF LOG LEVELS

||| We store the requested log levels in a Trie which makes it easy to check
||| whether a given log level is captured by the user's request for information.
export
LogLevels : Type
LogLevels = StringTrie Nat

||| By default we log everything but with very few details (i.e. next to nothing)
export
defaultLogLevel : LogLevels
defaultLogLevel = singleton [] 0

export
insertLogLevel : LogLevel -> LogLevels -> LogLevels
insertLogLevel (MkLogLevel ps n) = insert ps n

----------------------------------------------------------------------------------
-- CHECKING WHETHER TO LOG

||| We keep a log if there is a prefix of its path associated to a larger number
||| in the LogLevels.
export
keepLog : LogLevel -> LogLevels -> Bool
keepLog (MkLogLevel _ Z) _ = True
keepLog (MkLogLevel path n) levels = go path levels where

  go : List String -> StringTrie Nat -> Bool
  go path (MkStringTrie current) = here || there where

    here : Bool
    here = case fromThis current of
      Nothing => False
      Just m  => n <= m

    there : Bool
    there = case path of
      [] => False
      (p :: rest) => fromMaybe False $ do
        assoc <- fromThat current
        next  <- lookup p assoc
        pure $ go rest next
