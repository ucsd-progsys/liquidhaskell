module Language.Haskell.Liquid.Constraint.ToFixpoint (

    cgInfoFInfo

  , fixConfig

  ) where

import           Prelude hiding (error)
import           Data.Monoid

import qualified Language.Fixpoint.Types.Config as FC
import           System.Console.CmdArgs.Default (def)
import qualified Language.Fixpoint.Types        as F
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Types hiding     ( binds )
import           Language.Fixpoint.Solver                 ( parseFInfo )
import           Language.Haskell.Liquid.Constraint.Qualifier
-- import           Language.Fixpoint.Misc (traceShow)

import Language.Haskell.Liquid.UX.Config (allowSMTInstationation)
import Data.Maybe (fromJust)

fixConfig :: FilePath -> Config -> FC.Config
fixConfig tgt cfg = def
  { FC.solver           = fromJust (smtsolver cfg)
  , FC.linear           = linear            cfg
  , FC.eliminate        = eliminate         cfg
  , FC.nonLinCuts       = not (higherOrderFlag cfg) -- eliminate cfg /= FC.All
  , FC.save             = saveQuery         cfg
  , FC.srcFile          = tgt
  , FC.cores            = cores             cfg
  , FC.minPartSize      = minPartSize       cfg
  , FC.maxPartSize      = maxPartSize       cfg
  , FC.elimStats        = elimStats         cfg
  , FC.elimBound        = elimBound         cfg
  , FC.allowHO          = higherOrderFlag   cfg
  , FC.allowHOqs        = higherorderqs     cfg
  , FC.extensionality   = extensionality    cfg || gradual cfg
  , FC.alphaEquivalence = alphaEquivalence  cfg
  , FC.betaEquivalence  = betaEquivalence   cfg
  , FC.normalForm       = normalForm        cfg
  , FC.stringTheory     = stringTheory      cfg
  , FC.gradual          = gradual           cfg 
  , FC.interactive      = interactive       cfg 
  }


cgInfoFInfo :: GhcInfo -> CGInfo -> IO (F.FInfo Cinfo)
cgInfoFInfo info cgi = do
  let tgtFI  = targetFInfo info cgi
  impFI     <- ignoreQualifiers info <$> parseFInfo (hqFiles info)
  return       (tgtFI <> impFI)
  -- let fI    = ignoreQualifiers info (tgtFI <> impFI)
  -- return fI

ignoreQualifiers :: GhcInfo -> F.FInfo a -> F.FInfo a
ignoreQualifiers info fi
  | useSpcQuals info = fi
  | otherwise        = fi { F.quals = [] }

-- NOPROP ignoreQualifiers :: GhcInfo -> F.FInfo a -> F.FInfo a
-- NOPROP ignoreQualifiers info fi
  -- NOPROP | noQuals     = fi { F.quals = [] }
  -- NOPROP | otherwise   = fi
  -- NOPROP where noQuals = (FC.All == ) . eliminate . getConfig . spec $ info

targetFInfo :: GhcInfo -> CGInfo -> F.FInfo Cinfo
targetFInfo info cgi = F.fi cs ws bs ls consts ks qs bi aHO aHOqs es 
  where
    cs               = fixCs    cgi
    ws               = fixWfs   cgi
    bs               = binds    cgi
    ls               = fEnv     cgi
    consts           = cgConsts cgi
    ks               = kuts     cgi
    qs               = qualifiers info (fEnv cgi)
    bi               = (\x -> Ci x Nothing Nothing) <$> bindSpans cgi
    aHO              = allowHO cgi
    aHOqs            = higherOrderFlag info
    es               = makeAxioms info 

makeAxioms :: GhcInfo -> [F.Triggered F.Expr]
makeAxioms info 
  | allowSMTInstationation (getConfig info)
  = F.defaultTrigger . axiomEq <$> gsAxioms (spec info)
  | otherwise
  = [] 
