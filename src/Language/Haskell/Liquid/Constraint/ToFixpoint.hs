module Language.Haskell.Liquid.Constraint.ToFixpoint (

	cgInfoFInfo

	) where

import qualified Language.Fixpoint.Types        as F
import Language.Haskell.Liquid.Constraint.Types

import Language.Haskell.Liquid.Types hiding     ( binds )
import Language.Fixpoint.Misc                   ( mapSnd )
import Language.Fixpoint.Interface              ( parseQualifiers )

-- import           Control.Applicative ((<$>))
import qualified Data.HashMap.Strict            as M

import Language.Haskell.Liquid.Qualifier
import Language.Haskell.Liquid.RefType          ( rTypeSortedReft )


cgInfoFInfo :: GhcInfo -> CGInfo -> IO (F.FInfo Cinfo)
cgInfoFInfo info cgi = do
  qs    <- ghcQuals info
  return F.FI { F.cm    = M.fromList $ F.addIds $ fixCs cgi
              , F.ws    = fixWfs cgi
              , F.bs    = binds cgi
              , F.gs    = F.fromListSEnv . map mkSort $ meas spc
              , F.lits  = lits cgi
              , F.kuts  = kuts cgi
              , F.quals = qs }
   where
    spc    = spec info
    tce    = tcEmbeds spc
    mkSort = mapSnd (rTypeSortedReft tce . val)

ghcQuals :: GhcInfo -> IO [F.Qualifier]
ghcQuals info = do
    let spcQs = qualifiers spc
    let genQs = specificationQualifiers n info
    impQs    <- parseQualifiers $ hqFiles info
    return    $ impQs ++ spcQs ++ genQs
  where
    n         = maxParams $ config spc
    spc       = spec info
