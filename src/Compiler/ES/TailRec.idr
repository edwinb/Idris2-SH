||| Tail-call optimization.
|||
||| Here is a lengthy explanation how this works at the
||| moment. Assume the following call graph of functions f1,f2,f3,f4 all
||| calling each other in tail call position:
|||
||| ```
|||       ------------ f2 ---- f4 (result)
|||      /          /     \
||| f1 ---- f1     /       -- f1
|||      \        /
|||       -- f3 --
||| ```
|||
||| First, a directed graph of all toplevel function calls
||| (incoming and outgoing) in tail-call position is created:
|||
||| ```idris
||| MkCallGraph $ fromList [(f1,[f1,f2,f3]),(f2,[f1,f4]),(f3,[f2])]
|||             $ fromList [(f1,[f1,f2]),(f2,[f1,f3]),(f3,[f1]),(f4,[f2])]
||| ```
|||
||| Mutually tail-recursive functions form a strongly connected
||| component in such a call graph: There is a (directed) path from every function
||| to every other function. Tarjan's algorithm is used to identify
||| these strongly connected components and grouping them in
||| a `List` of `List1`s.
|||
||| A tail-recursive group of functions is now converted to an imperative
||| loop as follows: Let `obj={h:_, a1:_, a2:_, ...}`
||| be a Javascript object consisting
||| of a tag `h` and arguments `a1`,`a2`,... . `h` indicates, whether `obj.a1`
||| contains the result of the computation (`h = 0`) or describes
||| a continuation indicating the next function to be invoked, in which
||| case fields `a1`,`a2`,... are the function's arguments.
||| together with the necessary arguments. The group of mutually
||| recursive functions is now converted to a single switch statement
||| where each branch corresponds to one of the function.
||| Each function will be changed in such a way that instead of
||| (recursively) calling another function in its group it will return
||| a new object `{h:_, a1:_, ...}` with `h` indicating the next
||| function to call (the next branch to choose in the `switch`
||| statement and `a1`,`a2`,... being the next function's set of
||| arguments. The function and initial argument object will then
||| be passed to toplevel function `__tailRec`, which loops
||| until the object signals that we have arrived at a result.
|||
||| Here is an example of two mutually tail-recursive functions
||| together with the generated tail-call optimized code.
|||
||| Original version:
|||
||| ```javascript
||| function isEven(arg){
|||   switch (arg) {
|||     case 0  : return 1;
|||     default : return isOdd(arg - 1);
|||   }
||| }
|||
||| function isOdd(arg){
|||   switch (arg) {
|||     case 0  : return 0;
|||     default : return isEven(arg - 1);
|||   }
||| }
||| ```
|||
||| The above gets converted to code similar to
||| the following.
|||
||| ```javascript
||| function tcOpt(arg) {
|||   switch(arg.h) {
|||   // former function isEven
|||   case 1: {
|||     switch (arg.a1) {
|||       case 0  : return {h: 0, a1: 1};
|||       default : return {h: 2, a1: arg.a1 - 1};
|||     }
|||   }
|||   // former function isOdd
|||   case 2: {
|||     switch (a1) {
|||       case 0  : return {h: 0, a1: 0};
|||       default : return {h: 1, a1: arg.a1 - 1};
|||     }
|||   }
||| }
|||
||| function isEven(arg){
|||   return __tailRec(tcOpt,{h: 1, a1: arg})
||| }
|||
||| function isOdd(arg){
|||   return __tailRec(tcOpt,{h: 2, a1: arg})
||| }
||| ```
|||
||| Finally, `__tailRec` is implemented as follows:
|||
||| ```javascript
|||   function __tailRec(f,ini) {
|||     let obj = ini;
|||     while(true){
|||       switch(obj.h){
|||         case 0: return obj.a1;
|||         default: obj = f(obj);
|||       }
|||     }
|||   }
||| ```
|||
||| While the above example is in Javascript, this module operates
||| on `NamedCExp` exclusively, so it might be used with any backend
||| where the things described above can be expressed.
module Compiler.ES.TailRec

import Data.Maybe
import Data.List
import Data.List1
import Data.String
import Libraries.Data.Graph
import Libraries.Data.SortedSet
import Libraries.Data.List.Extra as L
import Libraries.Data.SortedMap as M
import Core.Name
import Core.CompileExpr
import Core.Context

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

-- indices of a list starting at 1
indices : List a -> List Int
indices as = [1 .. cast (length as)]

zipWithIndices : List a -> List (Int,a)
zipWithIndices as = zip (indices as) as

--------------------------------------------------------------------------------
--          Tailcall Graph
--------------------------------------------------------------------------------

||| A (toplevel) function in a group of mutually tail recursive functions.
public export
record TcFunction where
  constructor MkTcFunction
  ||| Function's name
  name  : Name

  ||| Function's index in its tail call group
  ||| This is used to decide on which branch to choose in
  ||| the next iteration
  index : Int

  ||| Argument list
  args  : List Name

  ||| Function's definition
  exp   : NamedCExp

||| A group of mutually tail recursive toplevel functions.
public export
record TcGroup where
  constructor MkTcGroup
  ||| Index of the group. This is used to generate a uniquely
  ||| named tail call optimized toplevel function.
  index     : Int

  ||| Set of mutually recursive functions.
  functions : SortedMap Name TcFunction

-- tail calls made from an expression
tailCalls : NamedCExp -> SortedSet Name
tailCalls (NmLet _ _ _ z) = tailCalls z
tailCalls (NmApp _ (NmRef _ x) _) = singleton x
tailCalls (NmConCase fc sc xs x) =
  concatMap (\(MkNConAlt _ _ _ _ x) => tailCalls x) xs <+>
  concatMap tailCalls x
tailCalls (NmConstCase fc sc xs x) =
  concatMap (\(MkNConstAlt _ x) => tailCalls x) xs <+>
  concatMap tailCalls x
tailCalls _ = empty

-- Checks if a `List1` of functions actually has any tail recursive
-- function calls and needs to be optimized.
-- In case of a larger group (more than one element)
-- the group contains tailcalls by construction. In case
-- of a single function, we need to check that at least one
-- outgoing tailcall goes back to the function itself.
-- We use the given mapping from `Name` to set of names
-- called in tail position to verify this.
hasTailCalls : SortedMap Name (SortedSet Name) -> List1 Name -> Bool
hasTailCalls g (x ::: Nil) = maybe False (contains x) $ lookup x g
hasTailCalls _ _           = True

-- Given a strongly connected group of functions, plus
-- a unique index, convert them to a list of
-- consisting of the function names plus the `TcGroup`,
-- to which they belong.
toGroup :  SortedMap Name (Name,List Name,NamedCExp)
        -> (Int,List1 Name)
        -> List (Name,TcGroup)
toGroup funMap (groupIndex,functions) =
  let ns    = zipWithIndices $ forget functions
      group = MkTcGroup groupIndex . fromList $ mapMaybe fun ns
   in (,group) <$> forget functions
  where fun : (Int,Name) -> Maybe (Name,TcFunction)
        fun (fx, n) = do
          (_,args,exp) <- lookup n funMap
          pure (n,MkTcFunction n fx args exp)

-- Returns the connected components of the tail call graph
-- of a set of toplevel function definitions.
-- Every function name that is part of a tail-call group
-- (a set of mutually tail-recursive functions)
-- points to its corresponding group.
tailCallGroups :  List (Name,List Name,NamedCExp)
               -> SortedMap Name TcGroup
tailCallGroups funs =
  let funMap = M.fromList $ map (\t => (fst t,t)) funs
      graph  = map (\(_,_,x) => tailCalls x) funMap
      groups = filter (hasTailCalls graph) $ tarjan graph
   in fromList $ concatMap (toGroup funMap) (zipWithIndices groups)

--------------------------------------------------------------------------------
--          Converting tail call groups to expressions
--------------------------------------------------------------------------------

public export
record Function where
  constructor MkFunction
  name : Name
  args : List Name
  body : NamedCExp

tcFunction : Int -> Name
tcFunction = MN "$tcOpt"

tcArgName : Name
tcArgName = MN "$a" 0

tcContinueName : (groupIndex : Int) -> (functionIndex : Int) -> Name
tcContinueName gi fi = MN ("TcContinue" ++ show gi) fi

tcDoneName : (groupIndex : Int) -> Name
tcDoneName gi = MN "TcDone" gi

-- Converts a single function in a mutually tail-recursive
-- group of functions to a single branch in a pattern match.
-- Recursive function calls will be replaced with an
-- applied data constructor whose tag indicates the
-- branch in the pattern match to use next, and whose values
-- will be used as the arguments for the next function.
conAlt : TcGroup -> TcFunction -> NamedConAlt
conAlt (MkTcGroup tcIx funs) (MkTcFunction n ix args exp) =
  let name = tcContinueName tcIx ix
   in MkNConAlt name DATACON ix args (toTc exp)

   where mutual
     -- this is returned in case we arrived at a result
     -- (an expression not corresponding to a recursive
     -- call in tail position).
     tcDone : NamedCExp -> NamedCExp
     tcDone x = NmCon EmptyFC (tcDoneName tcIx) DATACON 0 [x]

     -- this is returned in case we arrived at a resursive call
     -- in tail position. The index indicates the next "function"
     -- to call, the list of expressions are the function's
     -- arguments.
     tcContinue : (index : Int) -> List NamedCExp -> NamedCExp
     tcContinue ix = NmCon EmptyFC (tcContinueName tcIx ix) DATACON ix

     -- recursively converts an expression. Only the `NmApp` case is
     -- interesting, the rest is pretty much boiler plate.
     toTc : NamedCExp -> NamedCExp
     toTc (NmLet fc x y z) = NmLet fc x y $ toTc z
     toTc x@(NmApp _ (NmRef _ n) xs) =
       case lookup n funs of
         Just v  => tcContinue v.index xs
         Nothing => tcDone x
     toTc (NmConCase fc sc a d) = NmConCase fc sc (map con a) (map toTc d)
     toTc (NmConstCase fc sc a d) = NmConstCase fc sc (map const a) (map toTc d)
     toTc x@(NmCrash _ _) = x
     toTc x = tcDone x

     con : NamedConAlt -> NamedConAlt
     con (MkNConAlt x y tag xs z) = MkNConAlt x y tag xs (toTc z)

     const : NamedConstAlt -> NamedConstAlt
     const (MkNConstAlt x y) = MkNConstAlt x (toTc y)

-- Converts a group of mutually tail recursive functions
-- to a list of toplevel function declarations. `tailRecLoopName`
-- is the name of the toplevel function that does the
-- infinite looping (function `__tailRec` in the example at
-- the top of this module).
convertTcGroup : (tailRecLoopName : Name) -> TcGroup -> List Function
convertTcGroup loop g@(MkTcGroup gindex fs) =
  let functions = sortBy (comparing index) $ values fs
      branches  = map (conAlt g) functions
      switch    = NmConCase EmptyFC (local tcArgName) branches Nothing
   in MkFunction tcFun [tcArgName] switch :: map toFun functions

  where tcFun : Name
        tcFun = tcFunction gindex

        local : Name -> NamedCExp
        local = NmLocal EmptyFC

        toFun : TcFunction -> Function
        toFun (MkTcFunction n ix args x) =
          let exps  = map local args
              tcArg = NmCon EmptyFC (tcContinueName gindex ix)
                        DATACON ix exps
              tcFun = NmRef EmptyFC tcFun
              body  = NmApp EmptyFC (NmRef EmptyFC loop) [tcFun,tcArg]
           in MkFunction n args body

-- Tail recursion optimizations: Converts all groups of
-- mutually tail recursive functions to an imperative loop.
tailRecOptim :  SortedMap Name TcGroup
             -> (tcLoopName : Name)
             -> List (Name,List Name,NamedCExp)
             -> List Function
tailRecOptim groups loop ts =
  let regular = mapMaybe toFun ts
      tailOpt = concatMap (convertTcGroup loop) $ values groups
   in tailOpt ++ regular

  where toFun : (Name,List Name,NamedCExp) -> Maybe Function
        toFun (n,args,exp) = case lookup n groups of
          Just _  => Nothing
          Nothing => Just $ MkFunction n args exp

||| Converts a list of toplevel definitions (potentially
||| several groups of mutually tail-recursive functions)
||| to a new set of tail-call optimized function definitions.
||| `MkNmFun`s are converted. Other constructors of `NamedDef`
||| are ignored and silently dropped.
export
functions :  (tcLoopName : Name)
          -> List (Name,FC,NamedDef)
          -> List Function
functions loop dfs =
  let ts = mapMaybe def dfs
   in tailRecOptim (tailCallGroups ts) loop ts
   where def : (Name,FC,NamedDef) -> Maybe (Name,List Name,NamedCExp)
         def (n,_,MkNmFun args x) = Just (n,args,x)
         def _                    = Nothing
