{-# LANGUAGE PatternGuards #-}

-- | Solve a system of horn-clause constraints ----------------------------

module Language.Fixpoint.Solver.Solve (solve) where

import           Control.Applicative ((<$>))
import qualified Data.HashMap.Strict  as M
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Config
import qualified Language.Fixpoint.Solver.Solution as S
import qualified Language.Fixpoint.Solver.Worklist as W
import           Language.Fixpoint.Solver.Monad

---------------------------------------------------------------------------
-- | The output of the Solver
---------------------------------------------------------------------------
type Result a = (F.FixResult (F.SubC a), M.HashMap F.Symbol F.Pred)
---------------------------------------------------------------------------

---------------------------------------------------------------------------
solve :: Config -> F.FInfo a -> IO (Result a)
---------------------------------------------------------------------------
solve cfg fi = runSolverM $ solve_ cfg fi

---------------------------------------------------------------------------
solve_ :: Config -> F.FInfo a -> SolveM (Result a)
---------------------------------------------------------------------------
solve_ cfg fi = refine fi s0 wkl >>= solutionResult fi
  where
    s0        = S.init cfg fi
    wkl       = W.init cfg fi

---------------------------------------------------------------------------
refine :: F.FInfo a -> S.Solution -> W.Worklist a -> SolveM S.Solution
---------------------------------------------------------------------------
refine fi s w
  | Just (c, w') <- W.pop w = do (b, s') <- refineC fi s c
                                 if b then refine fi s' (W.push c w')
                                      else return s'
  | otherwise               = return s


---------------------------------------------------------------------------
-- | Single Step Refinement -----------------------------------------------
---------------------------------------------------------------------------
refineC :: F.FInfo a -> S.Solution -> F.SubC a -> SolveM (Bool, S.Solution)
---------------------------------------------------------------------------
refineC fi s c = S.update s <$> filterValid lhs rhs
  where
    lhs        = lhsPred  fi s c
    rhs        = rhsCands    s c

lhsPred :: F.FInfo a -> S.Solution -> F.SubC a -> F.Pred
lhsPred = error "TODO"

rhsCands :: S.Solution -> F.SubC a -> Cand (Kvar, EQual)
rhsCands = error "TODO"

---------------------------------------------------------------------------
-- | Convert Solution into Result -----------------------------------------
---------------------------------------------------------------------------
solutionResult :: F.FInfo a -> S.Solution -> SolveM (Result a)
---------------------------------------------------------------------------
solutionResult = error "TODO"


