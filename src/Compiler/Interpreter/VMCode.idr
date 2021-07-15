module Compiler.Interpreter.VMCode


import Core.Core
import Core.Context
import Core.Context.Log
import Core.Primitives
import Core.Value
import Compiler.Common
import Compiler.VMCode
import Libraries.Data.IOArray
import Libraries.Data.NameMap
import Data.Nat
import Data.SnocList
import Data.Vect

public export
data Object : Type where
    Closure : (predMissing : Nat) -> (args : SnocList Object) -> Name -> Object
    Constructor : (tag : Int) -> (args : List Object) -> Object
    Const : Constant -> Object
    Null : Object

showType : Object -> String
showType (Closure _ _ _) = "Closure"
showType (Constructor _ _) = "Constructor"
showType (Const _) = "Constant"
showType Null = "Null"

mutual
    showSep : Nat -> List Object -> String
    showSep k [] = ""
    showSep k [o] = showDepth k o
    showSep k (o :: os) = showDepth k o ++ ", " ++ showSep k os

    showDepth : Nat -> Object -> String
    showDepth (S k) (Closure mis args fn) = show fn ++ "-" ++ show mis ++ "(" ++ showSep k (args <>> []) ++ ")"
    showDepth (S k) (Constructor t args) = "tag" ++ show t ++ "(" ++ showSep k args ++ ")"
    showDepth (S k) (Const c) = show c
    showDepth _ obj = showType obj

Show Object where
    show = showDepth 5

data State : Type where
record InterpState where
    constructor MkInterpState
    defs : NameMap VMDef
    locals : IOArray Object
    returnObj : Maybe Object

initInterpState : List (Name, VMDef) -> Core InterpState
initInterpState defsList = do
    let defs = fromList defsList
    locals <- coreLift $ newArray 0
    let returnObj = Nothing
    pure $ MkInterpState defs locals returnObj

0
Stack : Type
Stack = List Name

interpError : Ref State InterpState => Stack -> String -> Core a
interpError stk msg = do
    MkInterpState _ ls ret <- get State
    lsList <- coreLift $ toList ls
    throw $ InternalError $ "Interpreter Error in " ++ show (take 10 stk) ++ ":\n" ++ msg
        ++ "\n\nlocals:\n" ++ showWithIndex lsList
        ++ "\nreturn:\n  " ++ show ret
  where
    showWithIndex : forall a. {default 0 idx : Nat} -> Show a => List a -> String
    showWithIndex {idx} [] = ""
    showWithIndex {idx} (x :: xs) = "  " ++ show idx ++ ": " ++ show x ++ "\n" ++ showWithIndex {idx = S idx} xs

getReg : Ref State InterpState => Stack -> Reg -> Core Object
getReg stk (Loc i) = do
    ls <- locals <$> get State
    objm <- coreLift $ readArray ls i
    case objm of
        Just obj => pure obj
        Nothing =>
            interpError stk $ "Missing local " ++ show i
getReg stk RVal = do
    objm <- returnObj <$> get State
    case objm of
        Just obj => pure obj
        Nothing => interpError stk "Missing returnObj val"
getReg stk Discard = pure Null

setReg : Ref State InterpState => Stack -> Reg -> Object -> Core ()
setReg stk RVal obj = update State $ record { returnObj = Just obj }
setReg stk (Loc i) obj = do
    ls <- locals <$> get State
    when (i >= max ls) $ interpError stk $ "Attempt to set register: " ++ show i ++ ", size of locals: " ++ show (max ls)
    coreLift $ writeArray ls i obj
setReg stk Discard _ = pure ()

saveLocals : Ref State InterpState => Core a -> Core a
saveLocals act = do
    st <- get State
    x <- act
    put State st
    pure x

total
indexMaybe : List a -> Int -> Maybe a
indexMaybe [] _ = Nothing
indexMaybe (x :: xs) idx = if idx <= 0 then Just x else indexMaybe xs (idx - 1)

callPrim : Ref State InterpState => Stack -> PrimFn ar -> Vect ar Object -> Core Object
callPrim stk BelieveMe [_, _, obj] = pure obj
callPrim stk fn args = case the (Either Object (Vect ar Constant)) $ traverse getConst args of
    Right args' => case getOp {vars=[]} fn (NPrimVal EmptyFC <$> args') of
        Just (NPrimVal _ res) => pure $ Const res
        _ => interpError stk $ "OP: Error calling " ++ show (opName fn) ++ " with operands: " ++ show args'
    Left obj => interpError stk $ "OP: Expected Constant, found " ++ showType obj
  where
    getConst : Object -> Either Object Constant
    getConst (Const c) = Right c
    getConst o = Left o

NS_UN : Namespace -> String -> Name
NS_UN ns un = NS ns (UN un)

argError : Ref State InterpState => Stack -> Vect h Object -> Core a
argError stk obj = interpError stk $ "Unexpected arguments: " ++ foldMap ((" " ++) . showType) obj

unit : Object
unit = Const (I 0)

ioRes : Object -> Object
ioRes obj = Constructor 0 [Const WorldVal, obj]

-- TODO: add more?
knownForeign : NameMap (ar ** (Ref State InterpState => Stack -> Vect ar Object -> Core Object))
knownForeign = fromList
    [ (NS_UN ioNS "prim__putChar", (2 ** prim_putChar))
    , (NS_UN ioNS "prim__getChar", (1 ** prim_getChar))
    , (NS_UN ioNS "prim__getStr", (1 ** prim_getStr))
    , (NS_UN ioNS "prim__putStr", (2 ** prim_putStr))
    ]
  where
    prim_putChar : Ref State InterpState => Stack -> Vect 2 Object -> Core Object
    prim_putChar _ [Const (Ch c), Const WorldVal] = ioRes unit <$ coreLift_ (putChar c)
    prim_putChar stk as = argError stk as
    prim_getChar : Ref State InterpState => Stack -> Vect 1 Object -> Core Object
    prim_getChar _ [Const WorldVal] = ioRes . Const . Ch <$> coreLift getChar
    prim_getChar stk as = argError stk as
    prim_getStr : Ref State InterpState => Stack -> Vect 1 Object -> Core Object
    prim_getStr _ [Const WorldVal] = Const . Str <$> coreLift getLine
    prim_getStr stk as = argError stk as
    prim_putStr : Ref State InterpState => Stack -> Vect 2 Object -> Core Object
    prim_putStr _ [Const (Str s), Const WorldVal] = ioRes unit <$ coreLift_ (putStr s)
    prim_putStr stk as = argError stk as

knownExtern : NameMap (ar ** (Ref State InterpState => Stack -> Vect ar Object -> Core Object))
knownExtern = empty

beginFunction : Ref State InterpState => List (Int, Object) -> List VMInst -> Int -> Core (List VMInst)
beginFunction args (DECLARE (Loc i) :: is) maxLoc = beginFunction args is (Prelude.max i maxLoc)
beginFunction args (DECLARE _ :: is) maxLoc = beginFunction args is maxLoc
beginFunction args (START :: is) maxLoc = do
    locals <- coreLift $ newArray (maxLoc + 1)
    ignore $ traverse (\(idx, arg) => coreLift $ writeArray locals idx arg) args
    update State $ record { locals = locals, returnObj = Nothing }
    pure is
beginFunction args is maxLoc = pure is

parameters {auto c : Ref Ctxt Defs}
  mutual
    step : Stack -> Ref State InterpState => VMInst -> Core ()
    step stk (DECLARE _) = pure ()
    step stk START = pure ()
    step stk (ASSIGN target val) = do
        valObj <- getReg stk val
        setReg stk target valObj
    step stk (MKCON target tag args) = do
        argObjs <- traverse (getReg stk) args
        setReg stk target $ Constructor tag argObjs
    step stk (MKCLOSURE target fn missing args) = do
        argObjs <- traverse (getReg stk) args
        setReg stk target $ Closure (pred missing) ([<] <>< argObjs) fn
    step stk (MKCONSTANT target c) = setReg stk target $ Const c
    step stk (APPLY target fn arg) = do
        fnObj <- getReg stk fn
        argObj <- getReg stk arg
        case fnObj of
            Closure Z args fn => do
                res <- callFunc stk fn (args <>> [argObj])
                setReg stk target res
            Closure (S k) args fn => setReg stk target $ Closure k (args :< argObj) fn
            obj => interpError stk $ "APPLY: While applying " ++ show fn ++ ", expected closure, found: " ++ show obj
    step stk (CALL target _ fn args) = do
        argObjs <- traverse (getReg stk) args
        res <- callFunc stk fn argObjs
        setReg stk target res
    step stk (OP target fn args) = do
        argObjs <- traverseVect (getReg stk) args
        res <- callPrim stk fn argObjs
        setReg stk target res
    step stk (EXTPRIM target fn args) = case lookup fn knownExtern of
        Nothing => interpError stk $ "EXTPRIM: Unkown foreign function: " ++ show fn
        Just (ar ** op) => case toVect ar args of
            Nothing => interpError stk $ "EXTPRIM: Wrong number of arguments, found: " ++ show (length args) ++ ", expected: " ++ show ar
            Just argsVect => do
                argObjs <- traverseVect (getReg stk) argsVect
                res <- op stk argObjs
                setReg stk target res
    step stk (CASE sc alts def) = do
        scObj <- getReg stk sc
        case scObj of
            Constructor tag _ => matchCon stk tag alts def
            _ => interpError stk $ "CASE: Expected Constructor, found " ++ showType scObj
      where
        matchCon : Stack -> Int -> List (Int, List VMInst) -> Maybe (List VMInst) -> Core ()
        matchCon stk tag [] Nothing = interpError stk "CASE: Missing matching alternative or default"
        matchCon stk tag [] (Just is) = traverse_ (step stk) is
        matchCon stk tag ((t, is) :: alts) def =
            if tag == t
                then traverse_ (step stk) is
                else matchCon stk tag alts def
    step stk (CONSTCASE sc alts def) = do
        scObj <- getReg stk sc
        case scObj of
            Const c => matchConst stk c alts def
            _ => interpError stk $ "CONSTCASE: Expected Constant, found " ++ showType scObj
      where
        matchConst : Stack -> Constant -> List (Constant, List VMInst) -> Maybe (List VMInst) -> Core ()
        matchConst stk c [] Nothing = interpError stk "CONSTCASE: Missing matching alternative or default"
        matchConst stk c [] (Just is) = traverse_ (step stk) is
        matchConst stk c ((c', is) :: alts) def =
            if c == c'
                then traverse_ (step stk) is
                else matchConst stk c alts def
    step stk (PROJECT target val idx) = do
        valObj <- getReg stk val
        case valObj of
            Constructor _ args => case indexMaybe args idx of
                Nothing => interpError stk
                    $ "PROJECT: Unable to project index " ++ show idx
                    ++ ", missing arguments for constructor:\n" ++ show valObj
                Just arg => setReg stk target arg
            _ => interpError stk $ "PROJECT: Expected Constructor, found " ++ showType valObj
    step stk (NULL reg) = setReg stk reg Null
    step stk (ERROR msg) = interpError stk $ "ERROR: " ++ msg

    callFunc : Ref State InterpState => Stack -> Name -> List Object -> Core Object
    callFunc stk fn args = saveLocals $ do
        let ind = pack $ '|' <$ stk
        logCallStack <- logging "compiler.interpreter" 25
        when logCallStack $ coreLift $ putStrLn $ ind ++ "Calling " ++ show fn ++ " with args: " ++ show args
        let stk' = fn :: stk
        defs <- defs <$> get State
        res <- case lookup fn defs of
            Nothing => interpError stk $ "Undefined function: " ++ show fn
            Just (MkVMFun as is) => do
                when (length as /= length args) $ interpError stk
                    $ "Unexpected argument count during function call, expected: "
                    ++ show (length as) ++ ", found: " ++ show (length args)
                is' <- beginFunction (zip as args) is (foldl max (-1) as)
                traverse_ (step stk') is'
                getReg stk' RVal
            Just (MkVMForeign _ _ _) => case lookup fn knownForeign of
                Nothing => interpError stk $ "Unkown foreign function: " ++ show fn
                Just (ar ** op) => case toVect ar args of
                    Nothing => interpError stk $ "Wrong number of arguments, found: " ++ show (length args) ++ ", expected: " ++ show ar
                    Just argsVect => op stk argsVect
            Just (MkVMError is) => do
                traverse_ (step stk') is
                getReg stk' RVal
        when logCallStack $ coreLift $ putStrLn $ ind ++ "Result: " ++ show res
        pure res

compileExpr : Ref Ctxt Defs -> String -> String -> ClosedTerm -> String -> Core (Maybe String)
compileExpr _ _ _ _ _ = Nothing <$ throw {a=()} (InternalError "compile not implemeted for vmcode-interp")

executeExpr : Ref Ctxt Defs -> String -> ClosedTerm -> Core ()
executeExpr c _ tm = do
    cdata <- getCompileData False VMCode tm
    st <- newRef State !(initInterpState cdata.vmcode)
    ignore $ callFunc [] (MN "__mainExpression" 0) []

export
codegenVMCodeInterp : Codegen
codegenVMCodeInterp = MkCG compileExpr executeExpr Nothing Nothing
