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

import           Language.Fixpoint.Misc    (groupList)
import           Language.Fixpoint.Config  (Config, inFile, solver)
import qualified Language.Fixpoint.Types   as F
import qualified Language.Fixpoint.Errors  as E
import qualified Language.Fixpoint.Smt.Theories as Thy
import           Language.Fixpoint.Smt.Interface
import           Language.Fixpoint.Solver.Validate
import           Language.Fixpoint.Solver.Solution
import           Data.Maybe           (isJust, catMaybes)
-- import qualified Data.HashMap.Strict  as M
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
filterValid p qs =
  withContext $ \me ->
    smtBracket me $
      filterValid_ p qs me

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
declare fi  = withContext $ \me -> do
  xts      <- either E.die return $ declSymbols fi
  let ess   = declLiterals fi
  forM_ xts $ uncurry $ smtDecl     me
  forM_ ess $           smtDistinct me

declLiterals :: F.FInfo a -> [[F.Expr]]
declLiterals fi = [es | (_, es) <- tess ]
  where
    tess        = groupList [(t, F.expr x) | (x, t) <- F.lits fi]

declSymbols :: F.FInfo a -> Either E.Error [(F.Symbol, F.Sort)]
declSymbols = fmap dropThy . symbolSorts
  where
    dropThy = filter (not . isThy . fst)
    isThy   = isJust . Thy.smt2Symbol -- (`M.member` theorySymbols)
