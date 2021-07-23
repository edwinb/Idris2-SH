||| The content of this module is based on the paper
||| Applications of Applicative Proof Search
||| by Liam O'Connor

module Search.HDecidable

import Data.List.Lazy
import Data.List.Lazy.Quantifiers
import Data.List.Quantifiers
import Data.So

import Search.Negation

%default total

------------------------------------------------------------------------
-- Type, basic functions, and interface

||| Half a decider: when the search succeeds we bother building the proof
public export
record HDec (a : Type) where
  constructor MkHDec
  isTrue   : Bool
  evidence : So isTrue -> a

||| Happy path: we have found a proof!
public export
yes : a -> HDec a
yes = MkHDec True . const

||| Giving up
public export
no : HDec a
no = MkHDec False absurd

public export
fromDec : Dec a -> HDec a
fromDec (Yes p) = yes p
fromDec (No _) = no

public export
fromMaybe : Maybe a -> HDec a
fromMaybe = maybe no yes

public export
toMaybe : HDec a -> Maybe a
toMaybe (MkHDec True p) = Just (p Oh)
toMaybe (MkHDec False _) = Nothing

||| A type constructor satisfying AnHdec is morally an HDec i.e. we can
||| turn values of this type constructor into half deciders
||| It may be more powerful (like Dec) or more basic (like Maybe).

public export
interface AnHDec (0 t : Type -> Type) where
  toHDec : t a -> HDec a

public export AnHDec Dec where toHDec = fromDec
public export AnHDec HDec where toHDec = id
public export AnHDec Maybe where toHDec = fromMaybe

------------------------------------------------------------------------
-- Implementations

public export
Functor HDec where
  map f (MkHDec b prf) = MkHDec b (f . prf)

public export
Apply HDec where
  MkHDec False prff <*> _ = MkHDec False absurd
  _ <*> MkHDec False _ = MkHDec False absurd
  MkHDec True prff <*> MkHDec True prfx
    = yes (prff Oh (prfx Oh))

public export
Applicative HDec where
  pure = yes

||| Lazy in the second argument
public export
Alt HDec where
  p@(MkHDec True _) <|> _ = p
  _ <|> q = q

public export
Plus HDec where
  empty = no

public export
Alternative HDec where

public export
Bind HDec where
  MkHDec True x >>= f = f (x Oh)
  _ >>= _ = no

public export
Monad HDec where

public export
Show f => Show (HDec f) where
  show (MkHDec True p) = "True: " ++ show (p Oh)
  show _ = "False"

------------------------------------------------------------------------
-- Combinators

||| Half deciders are closed under product
public export
(&&) : (AnHDec l, AnHDec r) => l a -> r b -> HDec (a, b)
p && q = [| (toHDec p, toHDec q) |]

||| Half deciders are closed under sum
public export
(||) : (AnHDec l, AnHDec r) => l a -> r b -> HDec (Either a b)
p || q = [| Left (toHDec p) |] <|> [| Right (toHDec q) |]


||| Half deciders are closed negation. Here we use the `Negates` interface
||| so that we end up looking for *positive* evidence of something which is
||| much easier to find than negative one.
public export
not : (AnHDec l, Negates na a) => l na -> HDec (Not a)
not p = [| toNegation (toHDec p) |]


infixr 3 ==>

||| Half deciders are closed under implication
public export
(==>) : (AnHDec l, AnHDec r, Negates na a) => l na -> r b -> HDec (a -> b)
p ==> q = [| contra (not p) |] <|> [| const (toHDec q) |] where
  contra : Not a -> a -> b
  contra na a = void (na a)


namespace List

  ||| Half deciders are closed under the list quantifier any
  public export
  any : AnHDec l => (xs : List a) -> ((x : a) -> l (p x)) -> HDec (Any p xs)
  any [] p = no
  any (x :: xs) p = [| Here (toHDec (p x)) |] <|> [| There (any xs p) |]

  ||| Half deciders are closed under the list quantifier all
  public export
  all : AnHDec l => (xs : List a) -> ((x : a) -> l (p x)) -> HDec (All p xs)
  all [] p = yes []
  all (x :: xs) p = [| toHDec (p x) :: all xs p |]

namespace LazyList

  ||| Half deciders are closed under the lazy list quantifier any
  public export
  any : AnHDec l => (xs : LazyList a) -> ((x : a) -> l (p x)) -> HDec (Any p xs)
  any [] p = no
  any (x :: xs) p = [| Here (toHDec (p x)) |] <|> [| There (any xs p) |]
