module Language.Haskell.Liquid.Constraint.ToFixpoint (

  cgInfoFInfo

  ) where

import           Prelude hiding (error)
import           Data.Monoid
import qualified Language.Fixpoint.Types        as F
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Types hiding     ( binds )
import           Language.Fixpoint.Solver                 ( parseFInfo )
import           Language.Haskell.Liquid.Constraint.Qualifier
-- import           Language.Fixpoint.Misc (traceShow)

cgInfoFInfo :: GhcInfo -> CGInfo -> IO (F.FInfo Cinfo)
cgInfoFInfo info cgi = do
  let tgtFI = targetFInfo info cgi
  impFI    <- parseFInfo $ hqFiles info
  let fI    = ignoreQualifiers info (tgtFI <> impFI)
  return fI

ignoreQualifiers :: GhcInfo -> F.FInfo a -> F.FInfo a
ignoreQualifiers info fi
  | ignore     = fi { F.quals = [] }
  | otherwise  = fi
  where ignore = ignoreQuals . getConfig . spec $ info

targetFInfo :: GhcInfo -> CGInfo -> F.FInfo Cinfo
targetFInfo info cgi = F.fi cs ws bs ls consts ks qs bi aHO aHOqs
  where
    cs               = fixCs    cgi
    ws               = fixWfs   cgi
    bs               = binds    cgi
    ls               = fEnv     cgi
    consts           = cgConsts cgi
    ks               = kuts     cgi
    qs               = targetQuals info cgi
    bi               = (`Ci` Nothing) <$> bindSpans cgi
    aHO              = allowHO cgi
    aHOqs            = higherOrderFlag info

targetQuals :: GhcInfo -> CGInfo -> [F.Qualifier]
targetQuals info cgi = spcQs ++ genQs
  where
    spcQs     = gsQualifiers spc
    genQs     = specificationQualifiers n info (fEnv cgi)
    n         = maxParams $ getConfig spc
    spc       = spec info
