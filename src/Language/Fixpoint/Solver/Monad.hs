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
import           Control.Monad        (forM, forM_)
import           Data.Maybe           (catMaybes)
import           Control.Applicative  ((<$>))

---------------------------------------------------------------------------
-- | Solver Monadic API ---------------------------------------------------
---------------------------------------------------------------------------

type SolveM a = IO a

runSolverM :: F.BindEnv -> SolveM a -> IO a
runSolverM be act = error "TODO"

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

---------------------------------------------------------------------------
-- | SMT Interface --------------------------------------------------------
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
declare :: F.BindEnv -> SolveM ()
---------------------------------------------------------------------------
declare be = do
  me <- getContext
  forM_ (F.bindEnvToList be) $ \ (_, x, t) ->
    smtDecl me x [] (F.sr_sort t)

{- 1. xs    = syms p ++ syms qs
   2. decls = xs + env
   3. [decl x t | (x, t) <- decls]
  -}
