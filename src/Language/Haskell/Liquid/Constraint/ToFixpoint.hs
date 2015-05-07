module Language.Haskell.Liquid.Constraint.ToFixpoint (

	cgInfoFInfo

	) where

import qualified Language.Fixpoint.Types        as F
import Language.Haskell.Liquid.Constraint.Types

import Language.Haskell.Liquid.Types hiding     ( binds )
import Language.Fixpoint.Misc                   ( mapSnd )
import Language.Fixpoint.Interface              ( parseFInfo )

-- import           Control.Applicative ((<$>))
import qualified Data.HashMap.Strict            as M
import           Data.Monoid

import Language.Haskell.Liquid.Qualifier
import Language.Haskell.Liquid.RefType          ( rTypeSortedReft )

cgInfoFInfo :: GhcInfo -> CGInfo -> IO (F.FInfo Cinfo)
cgInfoFInfo info cgi = do
  let tgtFI = targetFInfo info cgi
  impFI    <- parseFInfo $ hqFiles info
  return    $ tgtFI <> impFI

--   qs    <- ghcQuals info
--   return F.FI { F.cm    = M.fromList $ F.addIds $ fixCs cgi
--               , F.ws    = fixWfs cgi
--               , F.bs    = binds cgi
--               , F.gs    = F.fromListSEnv . map mkSort $ meas spc
--               , F.lits  = lits cgi
--               , F.kuts  = kuts cgi
--               , F.quals = qs }
--    where
--     spc    = spec info
--     tce    = tcEmbeds spc
--     mkSort = mapSnd (rTypeSortedReft tce . val)

targetFInfo :: GhcInfo -> CGInfo -> F.FInfo Cinfo
targetFInfo info cgi
  = F.FI { F.cm    = M.fromList $ F.addIds $ fixCs cgi
         , F.ws    = fixWfs cgi
         , F.bs    = binds cgi
         , F.gs    = F.fromListSEnv . map mkSort $ meas spc
         , F.lits  = lits cgi
         , F.kuts  = kuts cgi
         , F.quals = targetQuals info }
   where
    spc    = spec info
    tce    = tcEmbeds spc
    mkSort = mapSnd (rTypeSortedReft tce . val)

targetQuals :: GhcInfo -> [F.Qualifier]
targetQuals info = spcQs ++ genQs
  where
    spcQs     = qualifiers spc
    genQs     = specificationQualifiers n info
    n         = maxParams $ config spc
    spc       = spec info



