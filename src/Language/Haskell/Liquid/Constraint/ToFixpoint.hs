module Language.Haskell.Liquid.Constraint.ToFixpoint (

  cgInfoFInfo

  ) where

import           Prelude hiding (error)
import           Data.Monoid
import qualified Language.Fixpoint.Types        as F
import           Language.Haskell.Liquid.Constraint.Types
-- import           Language.Fixpoint.Misc (traceShow)
import           Language.Haskell.Liquid.Types hiding     ( binds )
import           Language.Fixpoint.Solver                 ( parseFInfo )
import           Language.Haskell.Liquid.Constraint.Qualifier

cgInfoFInfo :: GhcInfo -> CGInfo -> FilePath -> IO (F.FInfo Cinfo)
cgInfoFInfo info cgi fi = do
  let tgtFI = targetFInfo info cgi fi
  impFI    <- parseFInfo $ hqFiles info
  return    $ tgtFI <> impFI

targetFInfo :: GhcInfo -> CGInfo -> FilePath -> F.FInfo Cinfo
targetFInfo info cgi fn = F.fi cs ws bs ls consts ks {- packs -} qs bi fn aHO aHOqs
  where
    -- packs               = F.makePack (kvPacks cgi)
    cs                  = fixCs    cgi
    ws                  = fixWfs   cgi
    bs                  = binds    cgi
    ls                  = fEnv     cgi
    consts              = cgConsts cgi
    ks                  = kuts     cgi
    qs                  = targetQuals info cgi
    bi                  = (`Ci` Nothing) <$> bindSpans cgi
    aHO                 = allowHO cgi
    aHOqs               = higherOrderFlag info

targetQuals :: GhcInfo -> CGInfo -> [F.Qualifier]
targetQuals info cgi = spcQs ++ genQs
  where
    spcQs     = gsQualifiers spc
    genQs     = specificationQualifiers n info (fEnv cgi)
    n         = maxParams $ getConfig spc
    spc       = spec info
    -- lEnv      = F.fromListSEnv $ lits cgi
