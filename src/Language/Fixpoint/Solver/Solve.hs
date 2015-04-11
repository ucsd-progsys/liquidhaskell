{-# LANGUAGE PatternGuards #-}

-- | Solve a system of horn-clause constraints ----------------------------

module Language.Fixpoint.Solver.Solve (solve) where

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
solve_ cfg fi = do
  let s0  = S.init cfg fi
  let wkl = W.init cfg fi
  refineSolution s0 wkl >>= solutionResult fi

---------------------------------------------------------------------------
refineSolution :: S.Solution -> W.Worklist a -> SolveM S.Solution
---------------------------------------------------------------------------
refineSolution s w
  | Just (c, w') <- W.pop w = do (b, s') <- refineC s c
                                 if b then refineSolution s' (W.push c w')
                                      else return s'
  | otherwise               = return s


---------------------------------------------------------------------------
-- | Single Step Refinement -----------------------------------------------
---------------------------------------------------------------------------
refineC :: S.Solution -> F.SubC a -> SolveM (Bool, S.Solution)
---------------------------------------------------------------------------
refineC = error "TODO"



---------------------------------------------------------------------------
-- | Convert Solution into Result -----------------------------------------
---------------------------------------------------------------------------
solutionResult :: F.FInfo a -> S.Solution -> SolveM (Result a)
---------------------------------------------------------------------------
solutionResult = error "TODO"


