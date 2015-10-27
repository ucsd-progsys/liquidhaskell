module Language.Haskell.Liquid.Constraint.ToFixpoint (

        cgInfoFInfo

        ) where

import qualified Language.Fixpoint.Types        as F
import Language.Haskell.Liquid.Constraint.Types

import Language.Haskell.Liquid.Types hiding     ( binds )
import Language.Haskell.Liquid.Misc             ( mapSnd )
import Language.Fixpoint.Interface              ( parseFInfo )

import           Control.Applicative ((<$>))
import qualified Data.HashMap.Strict            as M
import           Data.Monoid

import Language.Haskell.Liquid.Qualifier
import Language.Haskell.Liquid.RefType          ( rTypeSortedReft )

cgInfoFInfo :: GhcInfo -> CGInfo -> FilePath  -> IO (F.FInfo Cinfo)
cgInfoFInfo info cgi fi = do
  let tgtFI = targetFInfo info cgi fi
  impFI    <- parseFInfo $ hqFiles info
  return    $ tgtFI <> impFI

targetFInfo :: GhcInfo -> CGInfo -> FilePath -> F.FInfo Cinfo
targetFInfo info cgi fn = F.fi cs ws bs ls ks qs bi fn
  where 
   cs     = fixCs  cgi
   ws     = fixWfs cgi
   bs     = binds  cgi
   ls     = F.fromListSEnv $ lits cgi
   ks     = kuts cgi
   qs     = targetQuals info
   bi     = (`Ci` Nothing) <$> bindSpans cgi
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
