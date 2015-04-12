-- | This is a wrapper around IO that permits SMT queries

module Language.Fixpoint.Solver.Monad
       ( -- * Type
         SolveM

         -- * Execution
       , runSolverM

         -- * Get Binds
       , getBinds

         -- * SMT Query
       , filterValid
       )
       where

import qualified Language.Fixpoint.Types   as F
import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Solver.Solution
import           Control.Monad        (forM)
import           Data.Maybe           (catMaybes)
import           Control.Applicative  ((<$>))

---------------------------------------------------------------------------
filterValid :: F.Pred -> Cand a -> SolveM [a]
---------------------------------------------------------------------------
filterValid p qs = catMaybes <$> do
  me <- getContext
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracket me $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      return $ if valid then Just x else Nothing


---------------------------------------------------------------------------
-- | Solver Monad ---------------------------------------------------------
---------------------------------------------------------------------------

type SolveM a = IO a

runSolverM :: F.BindEnv -> SolveM a -> IO a
runSolverM be act = error "TODO"

declare :: F.FInfo a -> SolveM ()
declare = error "TODO"

{- 1. xs    = syms p ++ syms qs
   2. decls = xs + env
   3. [decl x t | (x, t) <- decls]
  -}




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
getContext :: SolveM Context
---------------------------------------------------------------------------
getContext = error "TODO"


