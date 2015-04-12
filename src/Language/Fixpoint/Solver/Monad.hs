-- | This is a wrapper around IO that permits SMT queries

module Language.Fixpoint.Solver.Monad
       ( -- * Type
         SolveM

         -- * Execution
       , runSolverM

         -- * SMT Query
       , filterValid

         -- * Access "Globals"
       , getBinds
       )
       where

import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Solver.Solution

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

---------------------------------------------------------------------------
getBinds :: SolveM F.BindEnv
---------------------------------------------------------------------------
getBinds = error "TODO"

---------------------------------------------------------------------------
filterValid :: F.FEnv -> F.Pred -> Cand a -> SolveM [a]
---------------------------------------------------------------------------
filterValid env p qs = error "TODO:filterValid"
  -- compute syms = syms p ++ syms qs
  -- compute decls using syms + env
