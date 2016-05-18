module Language.Haskell.Liquid.Constraint.ToFixpoint (

  cgInfoFInfo

  ) where
import Prelude hiding (error)
import qualified Language.Fixpoint.Types        as F
import Language.Haskell.Liquid.Constraint.Types

import Language.Haskell.Liquid.Types hiding     ( binds )

import Language.Fixpoint.Solver                 ( parseFInfo )



import           Data.Monoid

import Language.Haskell.Liquid.Constraint.Qualifier


cgInfoFInfo :: GhcInfo -> CGInfo -> FilePath  -> IO (F.FInfo Cinfo)
cgInfoFInfo info cgi fi = do
  let tgtFI = targetFInfo info cgi fi
  impFI    <- parseFInfo $ hqFiles info
  return    $ tgtFI <> impFI

targetFInfo :: GhcInfo -> CGInfo -> FilePath -> F.FInfo Cinfo
targetFInfo info cgi fn = F.fi cs ws bs ls ks qs bi fn aHO aHOqs 
  where
   cs     = fixCs  cgi
   ws     = fixWfs cgi
   bs     = binds  cgi
   ls     = fEnv cgi
   ks     = kuts cgi
   qs     = targetQuals info cgi
   bi     = (`Ci` Nothing) <$> bindSpans cgi
   aHO    = allowHO cgi 
   aHOqs  = higherorderqs $ config $ spec info 

targetQuals :: GhcInfo -> CGInfo -> [F.Qualifier]
targetQuals info cgi = spcQs ++ genQs
  where
    spcQs     = qualifiers spc
    genQs     = specificationQualifiers n info (fEnv cgi)
    n         = maxParams $ config spc
    spc       = spec info
    -- lEnv      = F.fromListSEnv $ lits cgi
