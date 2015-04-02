
-- | Solve a system of horn-clause constraints ----------------------------

module Language.Fixpoint.Solver.Solve (solve) where


import qualified Data.HashMap.Strict       as M
import qualified Language.Fixpoint.Types   as F
import           Language.Fixpoint.Config
import           Language.Fixpoint.Solver.Types 


---------------------------------------------------------------------------
solve :: Config -> F.FInfo a -> IO (Result a)
---------------------------------------------------------------------------
solve cfg fi = runSolverM $ solve_ cfg fi

---------------------------------------------------------------------------
solve_ :: Config -> F.FInfo a -> SolveM (Result a)
---------------------------------------------------------------------------
solve_ cfg fi = do
  let s0  = initSolution cfg fi
  let wkl = initWorklist cfg fi
  s      <- refineSolution s0 wkl
  return  $ solutionResult fi s 

refineSolution :: Solution -> Worklist a -> SolveM Solution
refineSolution s w
  | Just (c, w') <- popConstraint w
  = do (b, s') <- refineC s c
       if b then refineSolution s' (addDependencies c w) 
            else return s'
  | otherwise
  = return s

 
---------------------------------------------------------------------------
solutionResult :: F.FInfo a -> Solution -> Result a
---------------------------------------------------------------------------
solutionResult = undefined

---------------------------------------------------------------------------
initSolution :: Config -> F.FInfo a -> Solution
---------------------------------------------------------------------------
initSolution = error "TODO"

   
---------------------------------------------------------------------------
-- | Single Step Refinement -----------------------------------------------
---------------------------------------------------------------------------

refineC :: Solution -> F.SubC a -> SolveM (Bool, Solution)
refineC = error "TODO"

---------------------------------------------------------------------------
-- | Solver Monad ---------------------------------------------------------
---------------------------------------------------------------------------

data SolverState a = SoS { ssWorkList :: !(Worklist a)
                         , ssSolution :: !Solution
                         }


data SolveM a  = TODOSolveM

instance Monad SolveM where
  return = undefined
  (>>=)  = undefined
  
runSolverM :: SolveM a -> IO a
runSolverM = error "TODO"

