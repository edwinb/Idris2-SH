module Compiler.ES.Ast

import Core.CompileExpr
import Core.Context
import Compiler.Common
import Data.List1
import Data.Nat
import Data.Vect

%default total

||| A variable in a toplevel function definition
|||
||| When generating the syntax tree of imperative
||| statements and expressions, we decide - based on
||| codegen directives - which Idris names to keep
||| and which names to convert to short, mangled
||| versions.
public export
data Var =
    ||| An unaltered name - usually a toplevel function
    ||| or a function argument with an explicitly given
    ||| name
    VName Name |

    ||| Index of a local variables
    VLoc  Int  |

    ||| Index of a mangled toplevel function
    VRef  Int

||| A minimal expression.
public export
data Minimal =
  ||| A variable
  MVar Var |

  ||| A projection targeting the field of a data type.
  ||| We include these here since it allows us to
  ||| conveniently carry around a `SortedMap Name Minimal`
  ||| for name resolution during the generation of the
  ||| imperative syntax tree.
  MProjection Nat Minimal

--------------------------------------------------------------------------------
--          Expressions
--------------------------------------------------------------------------------

||| The effect of a statement or a block of statements.
||| `Returns` means the
||| result of the final expression will be returned as
||| the current function's result, while `ErrorWithout v`
||| is a reminder, that the block of code will eventually
||| assign a value to `v` and will fail to do so if
||| `v` hasn't previously been declared.
|||
||| This is used as a typelevel index to prevent us from
||| making some common stupid errors like declaring a variable
||| twice, or having several `return` statements in the same
||| block of code.
public export
data Effect = Returns | ErrorWithout Var

mutual
  ||| An expression in a function definition.
  public export
  data Exp : Type where
    ||| A variable or projection. Minimal expressions
    ||| will always be inlined unless explicitly bound
    ||| in an Idris2 `let` expression.
    EMinimal  : Minimal -> Exp

    ||| Lambda expression
    |||
    ||| An empty argument list represents a delayed computation
    ELam      : List Var -> Stmt (Just Returns) -> Exp

    ||| Function application.
    |||
    ||| In case of a zero-argument list, we might also be
    ||| dealing with forcing a delayed computation.
    EApp      : Exp -> List Exp -> Exp

    ||| Saturated construtor application.
    |||
    ||| The tag either represents the name of a type constructor
    ||| (when we are pattern matching on types) or the index
    ||| of a data constructor.
    ECon      : (tag : Int) -> ConInfo -> List Exp -> Exp

    ||| Primitive operation
    EOp       : {0 arity : Nat} -> PrimFn arity -> Vect arity Exp -> Exp

    ||| Externally defined primitive operation.
    EExtPrim  : Name -> List Exp -> Exp

    ||| A constant primitive.
    EPrimVal  : Constant -> Exp

    ||| An erased value.
    EErased   : Exp

  ||| An imperative statement in a function definition.
  |||
  ||| This is indexed over the `Effect` the statement,
  ||| will have.
  ||| An `effect` of `Nothing` means that the result of
  ||| the statement is `undefined`: The declaration of
  ||| a constant or assignment of a previously declared
  ||| variable. When we sequence statements in a block
  ||| of code, all but the last one of them must have
  ||| effect `Nothing`. This makes sure we properly declare variables
  ||| exactly once before eventually assigning them.
  ||| It makes also sure a block of code does not contain
  ||| several `return` statements (until they are the
  ||| results of the branches of a `switch` statement).
  public export
  data Stmt : (effect : Maybe Effect) -> Type where
    ||| Returns the result of the given expression.
    Return      : Exp -> Stmt (Just Returns)

    ||| Introduces a new constant by assigning the result
    ||| of a single expression to the given variable.
    Const      : (v : Var) -> Exp -> Stmt Nothing

    ||| Assigns the result of an expression to the given variable.
    ||| This will result in an error, if the variable has not
    ||| yet been declared.
    Assign     : (v : Var) -> Exp -> Stmt (Just $ ErrorWithout v)

    ||| Declares (but does not yet assign) a new mutable
    ||| variable. This is the only way to "saturate"
    ||| a `Stmt (Just $ ErrorWithout v)`.
    Declare    : (v : Var) -> Stmt (Just $ ErrorWithout v) -> Stmt Nothing

    ||| Switch statement from a pattern match on
    ||| data or type constructors. The result of each branch
    ||| will have the given `Effect`.
    |||
    ||| The scrutinee has already been lifted to
    ||| the outer scope to make sure it is only
    ||| evaluated once.
    ConSwitch   :  (e         : Effect)
                -> (scrutinee : Minimal)
                -> (alts      : List $ EConAlt e)
                -> (def       : Maybe $ Stmt $ Just e)
                -> Stmt (Just e)

    ||| Switch statement from a pattern on
    ||| a constant. The result of each branch
    ||| will have the given `Effect`.
    ConstSwitch :  (e         : Effect)
                -> (scrutinee : Exp)
                -> (alts      : List $ EConstAlt e)
                -> (def       : Maybe $ Stmt $ Just e)
                -> Stmt (Just e)

    ||| A runtime exception.
    Error       : {0 any : _} -> String -> Stmt (Just any)

    ||| A code block consisting of one or more
    ||| imperative statements.
    Block       :  List1 (Stmt Nothing) -> Stmt e -> Stmt e

  ||| Single branch in a pattern match on a data or
  ||| type constructor.
  public export
  record EConAlt (e : Effect) where
    constructor MkEConAlt
    tag     : Int
    conInfo : ConInfo
    body    : Stmt (Just e)

  ||| Single branch in a pattern match on a constant
  public export
  record EConstAlt (e : Effect) where
    constructor MkEConstAlt
    constant : Constant
    body     : Stmt (Just e)

export
toMinimal : Exp -> Maybe Minimal
toMinimal (EMinimal v) = Just v
toMinimal _            = Nothing

export
prepend : List (Stmt Nothing) -> Stmt (Just e) -> Stmt (Just e)
prepend []       s = s
prepend (h :: t) s = Block (h ::: t) s

export total
declare : {v : _} -> Stmt (Just $ ErrorWithout v) -> Stmt Nothing
declare (Assign v y)              = Const v y
declare (Block ss s)              = Block ss $ declare s
declare s                         = Declare v s
