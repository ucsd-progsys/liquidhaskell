{-# LANGUAGE PatternGuards #-}
module Language.Fixpoint.Solver.Solution
        ( -- * Solutions and Results
          Solution
        , Result

          -- * Initial Solution
        , init

          -- * Convert a Solution to a Result
        , result
        )
where


import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import           Data.Maybe                     (isNothing)
import           Language.Fixpoint.Config
import           Language.Fixpoint.Solver.Monad
import           Language.Fixpoint.Sort
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types        as F
import           Prelude                        hiding (init)

---------------------------------------------------------------------------
-- | Types ----------------------------------------------------------------
---------------------------------------------------------------------------

type Result a = (F.FixResult (F.SubC a), M.HashMap F.Symbol F.Pred)

type Solution = Sol KBind

type Sol a    = M.HashMap F.Symbol a

type KBind    = [EQual]

---------------------------------------------------------------------------
-- | Expanded or Instantiated Qualifier -----------------------------------
---------------------------------------------------------------------------

data EQual = EQ { eqQual :: !F.Qualifier
                , eqPred :: !F.Pred
                , eqArgs :: ![F.Expr]
                }
               deriving (Eq, Ord, Show)

{-@ data EQual = EQ { eqQual :: F.Qualifier
                    , eqPred :: F.Pred
                    , eqArgs :: {v: [F.Expr] | len v = len (q_params eqQual)}
                    }
  @-}

---------------------------------------------------------------------------
-- | Create Initial Solution from Qualifiers and WF constraints
---------------------------------------------------------------------------
init :: Config -> F.FInfo a -> Solution
---------------------------------------------------------------------------
init _ fi = L.foldl' (refine fi qs) s0 ws
  where
    s0    = M.empty
    qs    = F.quals fi
    ws    = F.ws    fi

refine :: F.FInfo a -> [F.Qualifier] -> Solution -> F.WfC a -> Solution
refine fi qs s w   = refineK (wfEnv fi w) qs s (wfKvar w)
  where

refineK env qs s (v, t, k) = M.insert k eqs' s
  where
    eqs'  = case M.lookup k s of
              Nothing  -> instK env qs v t k
              Just eqs -> [eq | eq <- eqs, okInst env v t eq]

instK env qs v t k = error "TODO"
{- 1. generate ALL xts combinations
   2. for each combination, instantiate, check SORT if ok then return it. -}

wfKvar :: F.WfC a -> (F.Symbol, F.Sort, F.Symbol)
wfKvar w@(F.WfC {F.wrft = sr})
  | F.Reft (v, F.Refa (F.PKVar k su)) <- F.sr_reft sr
  , F.isEmptySubst su = (v, F.sr_sort sr, k)
  | otherwise         = errorstar $ "wfKvar: malformed wfC " ++ show w

wfEnv :: F.FInfo a -> F.WfC a -> F.SEnv F.SortedReft
wfEnv = errorstar "TODO"

okInst :: F.SEnv F.SortedReft -> F.Symbol -> F.Sort -> EQual -> Bool
okInst env v t eq = isNothing $ checkSortedReftFull env sr
  where
    sr            = F.RR t (F.Reft (v, F.Refa (eqPred eq)))


---------------------------------------------------------------------------
-- | Convert Solution into Result
---------------------------------------------------------------------------
result :: F.FInfo a -> Solution -> SolveM (Result a)
---------------------------------------------------------------------------
result = error "TODO"
