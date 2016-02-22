module Language.Haskell.Liquid.Constraint.ToFixpoint (

        cgInfoFInfo

        ) where
import Prelude hiding (error)
import qualified Language.Fixpoint.Types        as F
import Language.Haskell.Liquid.Constraint.Types

import Language.Haskell.Liquid.Types hiding     ( binds )
import Language.Haskell.Liquid.Misc             ( mapSnd )
import Language.Fixpoint.Solver                 ( parseFInfo )

import           Control.Applicative ((<$>))
import qualified Data.HashMap.Strict            as M
import           Data.Monoid
import           Debug.Trace
import Language.Haskell.Liquid.Constraint.Qualifier
import Language.Haskell.Liquid.Types.RefType          ( rTypeSortedReft )

cgInfoFInfo :: GhcInfo -> CGInfo -> FilePath  -> IO (F.FInfo Cinfo)
cgInfoFInfo info cgi fi = do
  let tgtFI = targetFInfo info cgi fi
  impFI    <- parseFInfo $ hqFiles info
  return    $ tgtFI <> impFI

targetFInfo :: GhcInfo -> CGInfo -> FilePath -> F.FInfo Cinfo
targetFInfo info cgi fn = F.fi cs ws bs ls ks qs bi fn aHO 
  where
   cs     = fixCs  cgi
   ws     = fixWfs cgi
   bs     = binds  cgi
   ls     = fEnv cgi
   ks     = kuts cgi
   qs     = targetQuals info cgi
   bi     = (`Ci` Nothing) <$> bindSpans cgi
   aHO    = allowHO cgi 

targetQuals :: GhcInfo -> CGInfo -> [F.Qualifier]
targetQuals info cgi = spcQs ++ genQs
  where
    spcQs     = qualifiers spc
    genQs     = specificationQualifiers n info (fEnv cgi)
    n         = maxParams $ config spc
    spc       = spec info
    -- lEnv      = F.fromListSEnv $ lits cgi
