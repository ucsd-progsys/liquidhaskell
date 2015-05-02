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

         -- * Debug
       , tickIter

       )
       where

import           Language.Fixpoint.Config  (Config, inFile, solver)
import qualified Language.Fixpoint.Types   as F
import qualified Language.Fixpoint.Errors  as E
import           Language.Fixpoint.SmtLib2
import           Language.Fixpoint.Solver.Validate
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
runSolverM :: Config -> F.FInfo b -> SolveM a -> IO a
---------------------------------------------------------------------------
runSolverM cfg fi act = do
  ctx <-  makeContext (solver cfg) (inFile cfg)
  fst <$> runStateT (declare fi >> act) (SS ctx be 0)
  where
    be = F.bs fi

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

---------------------------------------------------------------------------
tickIter :: SolveM Int
---------------------------------------------------------------------------
tickIter = incIter >> getIter

withContext :: (Context -> IO a) -> SolveM a
withContext k = (lift . k) =<< getContext

getContext :: SolveM Context
getContext = ssCtx <$> get


---------------------------------------------------------------------------
-- | SMT Interface --------------------------------------------------------
---------------------------------------------------------------------------
filterValid :: F.Pred -> Cand a -> SolveM [a]
---------------------------------------------------------------------------
filterValid p qs = -- do
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
declare :: F.FInfo a -> SolveM ()
---------------------------------------------------------------------------
declare fi = withContext $ \me -> do
  xts <- either E.die return $ symbolSorts fi
  forM_ xts $ uncurry $ smtDecl me
