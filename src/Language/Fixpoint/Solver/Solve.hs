{-# LANGUAGE PatternGuards #-}

-- | Solve a system of horn-clause constraints ----------------------------

module Language.Fixpoint.Solver.Solve (solve) where

import qualified Data.HashMap.Strict  as M
import qualified Language.Fixpoint.Types as F

import           Language.Fixpoint.Config
import qualified Language.Fixpoint.Solver.Solution as S
import qualified Language.Fixpoint.Solver.Worklist as W


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

refineSolution :: Solution -> W.Worklist a -> SolveM Solution
refineSolution s w
  | Just (c, w') <- W.pop w
  = do (b, s') <- refineC s c
       if b then refineSolution s' (W.push c w')
            else return s'
  | otherwise
  = return s


---------------------------------------------------------------------------
-- | Step 2: Single Step Refinement ---------------------------------------
---------------------------------------------------------------------------

refineC :: Solution -> F.SubC a -> SolveM (Bool, Solution)
refineC = error "TODO"



---------------------------------------------------------------------------
-- | Step 3: Convert Solution into Result
---------------------------------------------------------------------------
solutionResult :: F.FInfo a -> Solution -> SolveM (Result a)
---------------------------------------------------------------------------
solutionResult = error "TODO"


---------------------------------------------------------------------------
-- | Solver Monad ---------------------------------------------------------
---------------------------------------------------------------------------

data SolverState a = SoS { ssWorkList :: !(W.Worklist a)
                         , ssSolution :: !Solution
                         }


data SolveM a  = TODOSolveM

instance Monad SolveM where
  return = error "TODO"
  (>>=)  = error "TODO"

runSolverM :: SolveM a -> IO a
runSolverM = error "TODO"

