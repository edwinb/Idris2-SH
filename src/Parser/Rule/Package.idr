module Parser.Rule.Package

import public Parser.Lexer.Package

import Data.List
import Data.List1

import Core.Name.Namespace

%default total

public export
Rule : Type -> Type
Rule = Grammar () Token True

public export
EmptyRule : Type -> Type
EmptyRule = Grammar () Token False

export
equals : Rule ()
equals = terminal "Expected equals" $
                  \case
                    Equals => Just ()
                    _ => Nothing

export
lte : Rule ()
lte = terminal "Expected <=" $
               \case
                 LTE => Just ()
                 _ => Nothing

export
gte : Rule ()
gte = terminal "Expected >=" $
               \case
                 GTE => Just ()
                 _ => Nothing

export
lt : Rule ()
lt = terminal "Expected <=" $
              \case
                LT => Just ()
                _ => Nothing

export
gt : Rule ()
gt = terminal "Expected >=" $
              \case
                GT => Just ()
                _ => Nothing

export
eqop : Rule ()
eqop = terminal "Expected ==" $
                \case
                  EqOp => Just ()
                  _ => Nothing

export
andop : Rule ()
andop = terminal "Expected &&" $
                 \case
                   AndOp => Just ()
                   _ => Nothing

export
eoi : Rule ()
eoi = terminal "Expected end of input" $
               \case
                 EndOfInput => Just ()
                 _ => Nothing

export
exactProperty : String -> Rule String
exactProperty p = terminal ("Expected property " ++ p) $
                           \case
                             DotSepIdent Nothing p' =>
                               if p == p' then Just p else Nothing
                             _ => Nothing

export
stringLit : Rule String
stringLit = terminal "Expected string" $
                     \case
                       StringLit str => Just str
                       _ => Nothing

export
integerLit : Rule Integer
integerLit = terminal "Expected integer" $
                      \case
                        IntegerLit i => Just i
                        _ => Nothing

export
namespacedIdent : Rule (Maybe Namespace, String)
namespacedIdent = terminal "Expected namespaced identifier" $
                           \case
                             DotSepIdent ns n => Just (ns, n)
                             _ => Nothing

export
moduleIdent : Rule ModuleIdent
moduleIdent = terminal "Expected module identifier" $
                       \case
                         DotSepIdent ns m =>
                           Just $ nsAsModuleIdent $
                                  mkNestedNamespace ns m
                         _ => Nothing

export
packageName : Rule String
packageName = terminal "Expected package name" $
                       \case
                         DotSepIdent Nothing str =>
                           if isIdent AllowDashes str
                              then Just str
                              else Nothing
                         _ => Nothing

export
dot' : Rule ()
dot' = terminal "Expected dot" $
                \case
                  Dot => Just ()
                  _ => Nothing

sep' : Rule ()
sep' = terminal "Expected separator" $
                \case
                  Separator => Just ()
                  _ => Nothing

export
sep : Rule t -> Rule (List t)
sep rule = forget <$> sepBy1 sep' rule
