module Language.Fixpoint.Solver.TrivialSort (simplify) where

import           Control.Arrow       (second)
import           Control.Applicative ((<$>))
import           Language.Fixpoint.Config
import           Language.Fixpoint.Types hiding (simplify, isNonTrivial)
import           Language.Fixpoint.Misc
import qualified Data.HashSet            as S
import qualified Data.HashMap.Strict     as M
import           Data.List (foldl')

-------------------------------------------------------------------------
simplify :: Config -> FInfo a -> FInfo a
-------------------------------------------------------------------------
simplify _ fi = simplifyFInfo (mkTrivialMap fi) fi

-------------------------------------------------------------------------
-- | The main data types
-------------------------------------------------------------------------
-- data Trivial = TrivialSort
             -- | NonTrivialSort
               -- deriving (Eq, Ord, Show)
--
-- instance Monoid Trivial where
  -- mempty                   = TrivialSort
  -- mappend _ NonTrivialSort = NonTrivialSort
  -- mappend NonTrivialSort _ = NonTrivialSort
  -- mappend _              _ = TrivialSort

type TrivialMap = S.HashSet Sort
type KVarMap    = M.HashMap KVar [KVar]
data Polarity   = Lhs | Rhs
type TrivInfo   = (TrivialMap, KVarMap)
-------------------------------------------------------------------------


-------------------------------------------------------------------------
mkTrivialMap :: FInfo a -> TrivialMap
-------------------------------------------------------------------------
mkTrivialMap fi = upd ti0
  where
    upd         = trivInfoMap . updTIFInfo fi
    ti0         = (S.empty, M.empty)

trivInfoMap :: TrivInfo -> TrivialMap
trivInfoMap = error "TODO"

updTIFInfo :: FInfo a -> TrivInfo -> TrivInfo
updTIFInfo fi = updTISubCs (M.elems $ cm fi)
              . updTIBinds (bs fi)

updTISubCs :: [SubC a] -> TrivInfo -> TrivInfo
updTISubCs cs ti = foldl' (flip updTISubC) ti cs

updTISubC :: SubC a -> TrivInfo -> TrivInfo
updTISubC c = updTI Lhs (slhs c) . updTI Rhs (srhs c)

updTIBinds :: BindEnv -> TrivInfo -> TrivInfo
updTIBinds be ti = foldl' (flip (updTI Lhs)) ti ts
  where
    ts           = [t | (_,_,t) <- bindEnvToList be]

updTI :: Polarity -> SortedReft -> TrivInfo -> TrivInfo
updTI = error "TODO"

{- 1. visit all SortedRefts
   2. mark $k as NonTrivial if
      $k |-> [sort]

 -}

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
isNonTrivial tm t = S.member t tm
