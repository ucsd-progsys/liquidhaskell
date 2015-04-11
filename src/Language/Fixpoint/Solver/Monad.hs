-- | This is a wrapper around IO that permits SMT queries

module Language.Fixpoint.Solver.Monad
       ( -- * Type
         SolveM

         -- * Execution
       , runSolverM

         -- * SMT Query
       , filterValid
       )
       where

import qualified Language.Fixpoint.Types as F

---------------------------------------------------------------------------
-- | Solver Monad ---------------------------------------------------------
---------------------------------------------------------------------------

type SolveM a = IO a

runSolverM :: SolveM a -> IO a
runSolverM x = x

-- instance Monad SolveM where
--   return            = SolveM . return
--   (SolveM x) >>= k  = SolveM $ do z <- x
--                                   let SolveM y = k z
--                                   y

filterValid :: F.Pred -> Cand a -> SolveM [a]
filterValid = error "TODO:filterValid"
