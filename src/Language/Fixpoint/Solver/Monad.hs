{-# LANGUAGE DeriveGeneric #-}

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
       , Stats
       , tickIter
       , stats
       , numIter
       )
       where

import           Control.DeepSeq
import           GHC.Generics
import           Language.Fixpoint.Utils.Progress
import           Language.Fixpoint.Misc    (groupList)
import           Language.Fixpoint.Types.Config  (Config, solver, real)
import qualified Language.Fixpoint.Types   as F
import qualified Language.Fixpoint.Types.Errors  as E
import qualified Language.Fixpoint.Smt.Theories as Thy
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Smt.Interface
import           Language.Fixpoint.Solver.Validate
import           Language.Fixpoint.Solver.Solution
import           Data.Maybe           (isJust, catMaybes)
import           Text.PrettyPrint.HughesPJ (text)
import           Control.Monad.State.Strict
import qualified Data.HashMap.Strict as M

---------------------------------------------------------------------------
-- | Solver Monadic API ---------------------------------------------------
---------------------------------------------------------------------------

type SolveM = StateT SolverState IO

data SolverState = SS { ssCtx     :: !Context          -- ^ SMT Solver Context
                      , ssBinds   :: !F.BindEnv        -- ^ All variables and types
                      , ssStats   :: !Stats            -- ^ Solver Statistics
                      }

data Stats = Stats { numCstr :: !Int -- ^ # Horn Constraints
                   , numIter :: !Int -- ^ # Refine Iterations
                   , numBrkt :: !Int -- ^ # smtBracket    calls (push/pop)
                   , numChck :: !Int -- ^ # smtCheckUnsat calls
                   , numVald :: !Int -- ^ # times SMT said RHS Valid
                   } deriving (Show, Generic)

instance NFData Stats

stats0    :: F.GInfo c b -> Stats
stats0 fi = Stats nCs 0 0 0 0
  where
    nCs   = M.size $ F.cm fi

instance PTable Stats where
  ptable s = DocTable [ (text "# Constraints"         , pprint (numCstr s))
                      , (text "# Refine Iterations"   , pprint (numIter s))
                      , (text "# SMT Push & Pops"     , pprint (numBrkt s))
                      , (text "# SMT Queries (Valid)" , pprint (numVald s))
                      , (text "# SMT Queries (Total)" , pprint (numChck s))
                      ]

---------------------------------------------------------------------------
runSolverM :: Config -> F.GInfo c b -> Int -> SolveM a -> IO a
---------------------------------------------------------------------------
runSolverM cfg fi t act = do
  ctx <-  makeContext (not $ real cfg) (solver cfg) file
  fst <$> runStateT (declare fi >> act) (SS ctx be $ stats0 fi)
  where
    be   = F.bs     fi
    file = F.fileName fi -- (inFile cfg)
---------------------------------------------------------------------------
getBinds :: SolveM F.BindEnv
---------------------------------------------------------------------------
getBinds = ssBinds <$> get

---------------------------------------------------------------------------
getIter :: SolveM Int
---------------------------------------------------------------------------
getIter = numIter . ssStats <$> get

---------------------------------------------------------------------------
incIter, incBrkt :: SolveM ()
---------------------------------------------------------------------------
incIter   = modifyStats $ \s -> s {numIter = 1 + numIter s}
incBrkt   = modifyStats $ \s -> s {numBrkt = 1 + numBrkt s}

---------------------------------------------------------------------------
incChck, incVald :: Int -> SolveM ()
---------------------------------------------------------------------------
incChck n = modifyStats $ \s -> s {numChck = n + numChck s}
incVald n = modifyStats $ \s -> s {numVald = n + numVald s}

withContext :: (Context -> IO a) -> SolveM a
withContext k = (lift . k) =<< getContext

getContext :: SolveM Context
getContext = ssCtx <$> get

modifyStats :: (Stats -> Stats) -> SolveM ()
modifyStats f = modify $ \s -> s { ssStats = f (ssStats s) }

---------------------------------------------------------------------------
-- | SMT Interface --------------------------------------------------------
---------------------------------------------------------------------------
filterValid :: F.Pred -> Cand a -> SolveM [a]
---------------------------------------------------------------------------
filterValid p qs = do
  qs' <- withContext $ \me ->
           smtBracket me $
             filterValid_ p qs me
  -- stats
  incBrkt
  incChck (length qs)
  incVald (length qs')
  return qs'



filterValid_ :: F.Pred -> Cand a -> Context -> IO [a]
filterValid_ p qs me = catMaybes <$> do
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracket me $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      return $ if valid then Just x else Nothing

---------------------------------------------------------------------------
declare :: F.GInfo c a -> SolveM ()
---------------------------------------------------------------------------
declare fi  = withContext $ \me -> do
  xts      <- either E.die return $ declSymbols fi
  let ess   = declLiterals fi
  forM_ xts $ uncurry $ smtDecl     me
  forM_ ess $           smtDistinct me

declLiterals :: F.GInfo c a -> [[F.Expr]]
declLiterals fi = [es | (_, es) <- tess ]
  where
    notFun      = not . F.isFunctionSortedReft . (`F.RR` F.trueReft)
    tess        = groupList [(t, F.expr x) | (x, t) <- F.toListSEnv $ F.lits fi, notFun t]

declSymbols :: F.GInfo c a -> Either E.Error [(F.Symbol, F.Sort)]
declSymbols = fmap dropThy . symbolSorts
  where
    dropThy = filter (not . isThy . fst)
    isThy   = isJust . Thy.smt2Symbol

---------------------------------------------------------------------------
stats :: SolveM Stats
---------------------------------------------------------------------------
stats = ssStats <$> get

---------------------------------------------------------------------------
tickIter :: Bool -> SolveM Int
---------------------------------------------------------------------------
tickIter newScc = progIter newScc >> incIter >> getIter

progIter :: Bool -> SolveM ()
progIter newScc = lift $ when newScc progressTick
