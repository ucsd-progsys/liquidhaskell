module Language.Haskell.Liquid.Constraint.ToFixpoint (

	cgInfoFInfo

	) where

import SrcLoc           (noSrcSpan)


import qualified Language.Fixpoint.Types        as F
import Language.Haskell.Liquid.Constraint.Types

import Language.Haskell.Liquid.Types hiding     ( binds )
import Language.Fixpoint.Misc                   ( mapSnd )

import qualified Data.HashMap.Strict            as M

import Language.Haskell.Liquid.Qualifier
import Language.Haskell.Liquid.RefType          ( rTypeSortedReft )


cgInfoFInfo :: GhcInfo -> CGInfo -> F.FInfo Cinfo
cgInfoFInfo info cgi
  = F.FI { F.cm    = M.fromList $ F.addIds $ fixCs cgi
         , F.ws    = fixWfs cgi  
         , F.bs    = binds cgi 
         , F.gs    = F.fromListSEnv . map mkSort $ meas spc
         , F.lits  = lits cgi 
         , F.kuts  = kuts cgi 
         , F.quals = (qualifiers $ spc) ++ (specificationQualifiers (maxParams (config spc)) info)
         }
   where  
    spc        = spec info
    tce        = tcEmbeds spc 
    mkSort     = mapSnd (rTypeSortedReft tce . val)
