-- | This is a wrapper around IO that permits SMT queries

module Language.Fixpoint.Solver.Monad
       ( -- * Type
         SolveM

         -- * Execution
       , runSolverM

         -- * Get Binds
       , getBinds
       , getIter

         -- * SMT Query
       , filterValid
       )
       where

import           Language.Fixpoint.Config  (Config, solver)
import qualified Language.Fixpoint.Types   as F
import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Solver.Solution
import           Data.Maybe           (catMaybes)
import           Control.Applicative  ((<$>))
import           Control.Monad.State.Strict

---------------------------------------------------------------------------
-- | Solver Monadic API ---------------------------------------------------
---------------------------------------------------------------------------

type SolveM = StateT SolverState IO

data SolverState = SS { ssCtx   :: !Context
                      , ssBinds :: !F.BindEnv
                      , ssIter  :: !Int
                      }

---------------------------------------------------------------------------
runSolverM :: Config -> F.BindEnv -> SolveM a -> IO a
---------------------------------------------------------------------------
runSolverM cfg be act = do
  ctx <-  makeContext (solver cfg)
  fst <$> runStateT (declare be >> act) (SS ctx be 0)

---------------------------------------------------------------------------
getBinds :: SolveM F.BindEnv
---------------------------------------------------------------------------
getBinds = ssBinds <$> get

---------------------------------------------------------------------------
getIter :: SolveM Int
---------------------------------------------------------------------------
getIter = ssIter <$> get

---------------------------------------------------------------------------
incIter :: SolveM ()
---------------------------------------------------------------------------
incIter = modify $ \s -> s {ssIter = 1 + ssIter s}


withContext :: (Context -> IO a) -> SolveM a
withContext k = (lift . k) =<< getContext

getContext :: SolveM Context
getContext = ssCtx <$> get


---------------------------------------------------------------------------
-- | SMT Interface --------------------------------------------------------
---------------------------------------------------------------------------
filterValid :: F.Pred -> Cand a -> SolveM [a]
---------------------------------------------------------------------------
filterValid p qs = do
  incIter
  withContext $ filterValid_ p qs

filterValid_ :: F.Pred -> Cand a -> Context -> IO [a]
filterValid_ p qs me = catMaybes <$> do
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracket me $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      return $ if valid then Just x else Nothing

---------------------------------------------------------------------------
declare :: F.BindEnv -> SolveM ()
---------------------------------------------------------------------------
declare be = withContext $ \me ->
  forM_ (F.bindEnvToList be) $ \ (_, x, t) ->
    smtDecl me x [] (F.sr_sort t)


{- 1. xs    = syms p ++ syms qs
   2. decls = xs + env
   3. [decl x t | (x, t) <- decls]
  -}
