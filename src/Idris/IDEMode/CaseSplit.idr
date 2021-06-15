module Idris.IDEMode.CaseSplit

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Metadata
import Core.TT
import Core.Value

import Parser.Lexer.Source
import Parser.Unlit

import TTImp.Interactive.CaseSplit
import TTImp.TTImp
import TTImp.Utils

import Idris.IDEMode.TokenLine
import Idris.REPL.Opts
import Idris.Resugar
import Idris.Syntax

import Data.List
import Data.List1
import Libraries.Data.List.Extra
import Libraries.Data.String.Extra
import Data.Strings
import System.File

%hide Data.Strings.lines
%hide Data.Strings.lines'
%hide Data.Strings.unlines
%hide Data.Strings.unlines'

%default covering

||| A series of updates is a mapping from `RawName` to `String`
||| `RawName` is currently just an alias for `String`
||| `String` is a rendered `List SourcePart`
Updates : Type
Updates = List (RawName, String)

||| Convert a RawImp update to a SourcePart one
toStrUpdate : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              (Name, RawImp) -> Core Updates
toStrUpdate (UN n, term)
    = do clause <- pterm term
         pure [(n, show (bracket clause))]
  where
    bracket : PTerm -> PTerm
    bracket tm@(PRef _ _) = tm
    bracket tm@(PList _ _ _) = tm
    bracket tm@(PSnocList _ _ _) = tm
    bracket tm@(PPair _ _ _) = tm
    bracket tm@(PUnit _) = tm
    bracket tm@(PComprehension _ _ _) = tm
    bracket tm@(PPrimVal _ _) = tm
    bracket tm = PBracketed emptyFC tm
toStrUpdate _ = pure [] -- can't replace non user names

data UPD : Type where

doUpdates : {auto u : Ref UPD (List String)} ->
            Defs -> Updates -> List SourcePart ->
            Core (List SourcePart)
doUpdates defs ups [] = pure []
doUpdates defs ups (LBrace :: xs)
    -- the cases we care about are easy to detect w/o whitespace, so separate it
    = let (ws, nws) = span isWhitespace xs in
         case nws of
           Name n :: RBrace :: rest =>
                -- expand something in braces into its cases, e.g.
                -- { x} where x : Nat, becomes { x = Z} (and later { x = (S k)})
                pure (LBrace :: ws ++
                      Name n ::
                      Whitespace " " :: Equal :: Whitespace " " ::
                      !(doUpdates defs ups (Name n :: RBrace :: rest)))
           Name n :: Equal :: rest =>
                -- update the RHS of the Equal, e.g. `rest` in {x = rest}
                pure (LBrace :: ws ++
                      Name n ::
                      Whitespace " " :: Equal :: Whitespace " " ::
                      !(doUpdates defs ups rest))
           Name n :: Whitespace s :: RBrace :: rest =>
                -- expand something in braces into its cases, e.g.
                -- { x} where x : Nat, becomes { x = Z} (and later { x = (S k)})
                map (LBrace :: ws ++) $
                pure $ (Name n ::
                      Whitespace " " :: Equal :: Whitespace " " ::
                      !(doUpdates defs ups (Name n :: Whitespace s :: RBrace :: rest)))
           -- not a special case: proceed as normal
           _ => map (LBrace :: [] ++) $ doUpdates defs ups xs
  where
    isWhitespace : SourcePart -> Bool
    isWhitespace (Whitespace _) = True
    isWhitespace _              = False

doUpdates defs ups (Name n :: xs)
    = case lookup n ups of
           Nothing => pure (Name n :: !(doUpdates defs ups xs))
           Just up => pure (Other up :: !(doUpdates defs ups xs))
doUpdates defs ups (HoleName n :: xs)
    = do used <- get UPD
         n' <- uniqueName defs used n
         put UPD (n' :: used)
         pure $ HoleName n' :: !(doUpdates defs ups xs)
doUpdates defs ups (x :: xs)
    = pure $ x :: !(doUpdates defs ups xs)

-- State here is a list of new hole names we generated (so as not to reuse any).
-- Update the token list with the string replacements for each match, and return
-- the newly generated strings.
updateAll : {auto u : Ref UPD (List String)} ->
            Defs -> List SourcePart -> List Updates ->
            Core (List String)
updateAll defs l [] = pure []
updateAll defs l (rs :: rss)
    = do l' <- doUpdates defs rs l
         rss' <- updateAll defs l rss
         pure (concatMap toString l' :: rss')

-- Turn the replacements we got from 'getSplits' into a list of actual string
-- replacements
getReplaces : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              List (Name, RawImp) -> Core Updates
getReplaces updates
    = do strups <- traverse toStrUpdate updates
         pure (concat strups)

showImpossible : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 (indent : Nat) -> RawImp -> Core String
showImpossible indent lhs
    = do clause <- pterm lhs
         pure (fastPack (replicate indent ' ') ++ show clause ++ " impossible")

-- Given a list of updates and a line and column, find the relevant line in
-- the source file and return the lines to replace it with
export
updateCase : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             List ClauseUpdate -> Int -> Int ->
             Core (List String)
updateCase splits line col
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => throw (InternalError "No file loaded")
              Just f =>
                do Right file <- coreLift $ readFile f
                       | Left err => throw (FileErr f err)
                   let thisline = elemAt (forget $ lines file) (integerToNat (cast line))
                   case thisline of
                        Nothing => throw (InternalError "File too short!")
                        Just l =>
                            do let valid = mapMaybe getValid splits
                               let bad = mapMaybe getBad splits
                               log "interaction.casesplit" 3 $ "Valid: " ++ show valid
                               log "interaction.casesplit" 3 $ "Bad: " ++ show bad
                               if isNil valid
                                  then do let indent = getIndent 0 $ fastUnpack l
                                          traverse (showImpossible indent) bad
                                  else do rs <- traverse getReplaces valid
                                          let stok = tokens l
                                          defs <- get Ctxt
                                          u <- newRef UPD (the (List String) [])
                                          updateAll defs stok rs
  where
    getValid : ClauseUpdate -> Maybe (List (Name, RawImp))
    getValid (Valid _ ups) = Just ups
    getValid _ = Nothing

    getBad : ClauseUpdate -> Maybe RawImp
    getBad (Impossible lhs) = Just lhs
    getBad _ = Nothing

    getIndent : (acc : Nat) -> List Char -> Nat
    getIndent acc [] = acc
    getIndent acc (' ' :: xs) = getIndent (acc + 1) xs
    getIndent acc _ = acc

fnName : Bool -> Name -> String
fnName lhs (UN n)
    = if isIdentNormal n then n
      else if lhs then "(" ++ n ++ ")"
      else "op"
fnName lhs (NS _ n) = fnName lhs n
fnName lhs (DN s _) = s
fnName lhs n = nameRoot n


export
getClause : {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto o : Ref ROpts REPLOpts} ->
            Int -> Name -> Core (Maybe String)
getClause l n
    = do defs <- get Ctxt
         Just (loc, nidx, envlen, ty) <- findTyDeclAt (\p, n => onLine (l-1) p)
             | Nothing => pure Nothing
         n <- getFullName nidx
         argns <- getEnvArgNames defs envlen !(nf defs [] ty)
         Just srcLine <- getSourceLine l
           | Nothing => pure Nothing
         let (mark, src) = isLitLine srcLine
         pure (Just (indent mark loc ++ fnName True n ++ concat (map (" " ++) argns) ++
                  " = ?" ++ fnName False n ++ "_rhs"))
  where
    indent : Maybe String -> NonEmptyFC -> String
    indent (Just mark) fc
        = relit (Just mark) $ pack (replicate (integerToNat (cast (max 0 (snd (startPos fc) - 1)))) ' ')
    indent Nothing fc = pack (replicate (integerToNat (cast (snd (startPos fc)))) ' ')
