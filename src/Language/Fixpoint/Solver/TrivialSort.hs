{-# LANGUAGE PatternGuards #-}
module Language.Fixpoint.Solver.TrivialSort (simplify) where

import           Control.Arrow       (second)
import           Control.Applicative ((<$>))
import           Language.Fixpoint.Config
import           Language.Fixpoint.Types hiding (simplify, isNonTrivial)
import           Language.Fixpoint.Misc
import qualified Data.HashMap.Strict     as M
import           Data.List               ((\\), sort)
import           Data.Maybe              (catMaybes)

-------------------------------------------------------------------------
simplify :: Config -> FInfo a -> FInfo a
-------------------------------------------------------------------------
simplify _ fi = simplifyFInfo (mkTrivialMap fi) fi

-------------------------------------------------------------------------
-- | The main data types
-------------------------------------------------------------------------
data Trivial = TrivialSort | NonTrivialSort deriving (Eq, Ord, Show)
type TrivialMap = M.HashMap Sort Trivial
-------------------------------------------------------------------------


-------------------------------------------------------------------------
mkTrivialMap :: FInfo a -> TrivialMap
-------------------------------------------------------------------------
mkTrivialMap = error "TODO"


-------------------------------------------------------------------------
simplifyFInfo :: TrivialMap -> FInfo a -> FInfo a
-------------------------------------------------------------------------
simplifyFInfo tm fi = fi {
     cm   = simplifySubC    tm <$> cm fi
   , ws   = simplifyWfCs    tm  $  ws fi
   , bs   = simplifyBindEnv tm  $  bs fi
   , gs   = simplifyFEnv    tm  $  gs fi
}

simplifyBindEnv :: TrivialMap -> BindEnv -> BindEnv
simplifyBindEnv = mapBindEnv . second . simplifySortedReft

simplifyFEnv :: TrivialMap -> FEnv -> FEnv
simplifyFEnv = fmap . simplifySortedReft

simplifyWfCs :: TrivialMap -> [WfC a] -> [WfC a]
simplifyWfCs tm = filter (isNonTrivial tm . sr_sort . wrft)

simplifySubC :: TrivialMap -> SubC a -> SubC a
simplifySubC tm c = c { slhs = slhs' , srhs = srhs' }
  where
    slhs'         = simplifySortedReft tm (slhs c)
    srhs'         = simplifySortedReft tm (srhs c)


simplifySortedReft :: TrivialMap -> SortedReft -> SortedReft
simplifySortedReft tm sr -- (RR s r)
  | nonTrivial = sr
  | otherwise  = sr { sr_reft = mempty }
  where
    nonTrivial = isNonTrivial tm (sr_sort sr)

isNonTrivial :: TrivialMap -> Sort -> Bool
isNonTrivial tm t
  | Just NonTrivialSort <- ti = True
  | Just TrivialSort    <- ti = False
  | _                   <- ti = True
  where
    ti                        = M.lookup t tm

{-
data FInfo a = FI { cm    :: M.HashMap Integer (SubC a)
                  , ws    :: ![WfC a]
                  , bs    :: !BindEnv
                  , gs    :: !FEnv
                  , lits  :: ![(Symbol, Sort)]
                  , kuts  :: Kuts
                  , quals :: ![Qualifier]
                  , bindInfo :: M.HashMap BindId a
                  }
               deriving (Show)

-}
