module Language.Haskell.Liquid.Constraint.ToFixpoint (

	cgInfoFInfo, cgInfoFInfoKvars

	) where

import SrcLoc           (noSrcSpan)


import qualified Language.Fixpoint.Types            as F
import Language.Haskell.Liquid.Constraint.Types

import Language.Haskell.Liquid.Types hiding (binds)

import qualified Data.HashMap.Strict as M

import Language.Haskell.Liquid.Qualifier

cgInfoFInfoKvars info cgi kvars = cgInfoFInfo info cgi{fixCs = fixCs' ++ trueCs}
  where 
    fixCs'                 = {- concatMap (updateCs kvars) -} (fixCs cgi) 
    trueCs                 = concatMap (`F.trueSubCKvar` (Ci noSrcSpan Nothing)) kvars


cgInfoFInfo :: GhcInfo -> CGInfo -> F.FInfo Cinfo
cgInfoFInfo info cgi
  = F.FI { F.cm    = M.fromList $ F.addIds $ fixCs cgi
         , F.ws    = fixWfs cgi  
         , F.bs    = binds cgi 
         , F.gs    = globals cgi 
         , F.lits  = lits cgi 
         , F.kuts  = kuts cgi 
         , F.quals = (qualifiers $ spec info) ++ (specificationQualifiers (maxParams (config $ spec info)) info)
--          , F.quals = specQuals cgi
         }

{-
updateCs kvars cs
  | null lhskvars || F.isFalse rhs
  = [cs] 
  | all (`elem` kvars) lhskvars && null lhsconcs
  = []
  | any (`elem` kvars) lhskvars
  = [F.removeLhsKvars cs kvars]
  | otherwise 
  = [cs]
  where lhskvars = F.reftKVars lhs
        rhskvars = F.reftKVars rhs
        lhs      = F.lhsCs cs
        rhs      = F.rhsCs cs
        F.Reft(_, lhspds) = lhs
        lhsconcs = [p | F.RConc p <- lhspds]

-}