module Core.Pattern

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Termination
import Libraries.Data.NameMap

%default covering

checkLHS : {vars : _} -> Term vars -> Bool
checkLHS app = all valid (getArgs app)
  where
    valid : forall vars . Term vars -> Bool
    valid (Local _ _ _ _) = True
    valid (As _ _ _ tm) = valid tm
    valid _ = False

export
addImplicitPattern : Ref Ctxt Defs
                  => FC -> Name -> Core ()
addImplicitPattern fc name = do
  log "pattern.implicit" 5 $ "Checking valid pattern synonym " ++ show !(toFullNames name)
  defs <- get Ctxt
  nidx <- checkUnambig fc name
  Just gdef <- lookupCtxtExact nidx defs.gamma
    | Nothing => undefinedName fc nidx
  IsTerminating <- checkTotal fc nidx
    | _ => throw $ GenericMsg fc "Pattern synonym must be total"
  let IsCovering = gdef.totality.isCovering
    | _ => throw $ GenericMsg fc "Pattern synonym must be total"
  let PMDef _ _ _ _ [(vs ** (env, lhs, rhs))] = gdef.definition
    | PMDef _ _ _ _ pats => throw $ GenericMsg fc $ "Pattern synonym must have a single definition, instead found " ++ show (length pats)
    | _ => throw $ GenericMsg fc "Pattern synonym must be a pattern-matching definition"
  let True = checkLHS lhs
    | False => throw $ GenericMsg fc $ "LHS of pattern synonym must contain only bindings"
  put Ctxt (record { patternSynonyms $= insert nidx () } defs)
