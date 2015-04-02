-- | This is a wrapper around IO that permits SMT queries

module Language.Fixpoint.Solver.Monad where

---------------------------------------------------------------------------
-- | Solver Monad ---------------------------------------------------------
---------------------------------------------------------------------------

data SolveM a  = TODOSolveM

instance Monad SolveM where
  return = error "TODO"
  (>>=)  = error "TODO"

runSolverM :: SolveM a -> IO a
runSolverM = error "TODO"

