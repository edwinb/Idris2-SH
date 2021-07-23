module Language.Reflection

import public Language.Reflection.TT
import public Language.Reflection.TTImp

%default total

||| Elaboration scripts
||| Where types/terms are returned, binders will have unique, if not
||| necessarily human readabe, names
export
data Elab : Type -> Type where
     Pure : a -> Elab a
     Bind : Elab a -> (a -> Elab b) -> Elab b
     Fail : String -> Elab a

     LogMsg : String -> Nat -> String -> Elab ()
     LogTerm : String -> Nat -> String -> TTImp -> Elab ()

     -- Elaborate a TTImp term to a concrete value
     Check : {expected : Type} -> TTImp -> Elab expected
     -- Quote a concrete expression back to a TTImp
     Quote : val -> Elab TTImp

     -- Elaborate under a lambda
     Lambda : (0 x : Type) ->
              {0 ty : x -> Type} ->
              ((val : x) -> Elab (ty val)) -> Elab ((val : x) -> (ty val))

     -- Get the current goal type, if known
     -- (it might need to be inferred from the solution)
     Goal : Elab (Maybe TTImp)
     -- Get the names of local variables in scope
     LocalVars : Elab (List Name)
     -- Generate a new unique name, based on the given string
     GenSym : String -> Elab Name
     -- Put a name in the current namespace
     InCurrentNS : Name -> Elab Name
     -- Get the types of every name which matches.
     -- There may be ambiguities - returns a list of fully explicit names
     -- and their types. If there's no results, the name is undefined.
     GetType : Name -> Elab (List (Name, TTImp))
     -- Get the type of a local variable
     GetLocalType : Name -> Elab TTImp
     -- Get the constructors of a data type. The name must be fully resolved.
     GetCons : Name -> Elab (List Name)
     -- Check a group of top level declarations
     Declare : List Decl -> Elab ()

export
Functor Elab where
  map f e = Bind e $ Pure . f

export
Apply Elab where
  f <*> a = Bind f (<$> a)

export
Applicative Elab where
  pure = Pure

export
Bind Elab where
  (>>=) = Bind

export
Monad Elab where

||| Report an error in elaboration
export
fail : String -> Elab a
fail = Fail

||| Write a log message, if the log level is >= the given level
export
logMsg : String -> Nat -> String -> Elab ()
logMsg = LogMsg

||| Write a log message and a rendered term, if the log level is >= the given level
export
logTerm : String -> Nat -> String -> TTImp -> Elab ()
logTerm = LogTerm

||| Log the current goal type, if the log level is >= the given level
export
logGoal : String -> Nat -> String -> Elab ()
logGoal str n msg
    = do g <- Goal
         case g of
              Nothing => pure ()
              Just t => logTerm str n msg t

||| Check that some TTImp syntax has the expected type
||| Returns the type checked value
export
check : {expected : Type} -> TTImp -> Elab expected
check = Check

||| Return TTImp syntax of a given value
export
quote : val -> Elab TTImp
quote = Quote

||| Build a lambda expression
export
lambda : (0 x : Type) ->
         {0 ty : x -> Type} ->
         ((val : x) -> Elab (ty val)) -> Elab ((val : x) -> (ty val))
lambda = Lambda

||| Get the goal type of the current elaboration
export
goal : Elab (Maybe TTImp)
goal = Goal

||| Get the names of the local variables in scope
export
localVars : Elab (List Name)
localVars = LocalVars

||| Generate a new unique name
export
genSym : String -> Elab Name
genSym = GenSym

||| Given a name, return the name decorated with the current namespace
export
inCurrentNS : Name -> Elab Name
inCurrentNS = InCurrentNS

||| Given a possibly ambiguous name, get all the matching names and their types
export
getType : Name -> Elab (List (Name, TTImp))
getType = GetType

||| Get the type of a local variable
export
getLocalType : Name -> Elab TTImp
getLocalType = GetLocalType

||| Get the constructors of a fully qualified data type name
export
getCons : Name -> Elab (List Name)
getCons = GetCons

||| Make some top level declarations
export
declare : List Decl -> Elab ()
declare = Declare
