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
import           Control.Monad.State.Strict
import           System.ProgressBar -- ( percentage, exact, startProgress, incProgress )
import           System.IO ( hSetBuffering, BufferMode(NoBuffering), stdout )

---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- | Solver Monadic API ---------------------------------------------------
---------------------------------------------------------------------------

type SolveM = StateT SolverState IO

data SolverState = SS { ssCtx     :: !Context
                      , ssBinds   :: !F.BindEnv
                      , ssIter    :: !Int
                      , ssProgRef :: !ProgressRef
                      }

---------------------------------------------------------------------------
runSolverM :: Config -> F.GInfo c b -> Integer -> SolveM a -> IO a
---------------------------------------------------------------------------
runSolverM cfg fi t act = do
  ctx <-  makeContext (solver cfg) (inFile cfg)
  hSetBuffering stdout NoBuffering
  (pr, _) <- startProgress percentage exact 80 t
  fst <$> runStateT (declare fi >> act) (SS ctx be 0 pr)
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
    isThy   = isJust . Thy.smt2Symbol -- (`M.member` theorySymbols)

---------------------------------------------------------------------------
tickIter :: Bool -> SolveM Int
---------------------------------------------------------------------------
tickIter newScc = do
  progress newScc
  incIter
  getIter

progress :: Bool -> SolveM ()
progress True  = do pr  <- ssProgRef <$> get
                    lift $ incProgress pr 1
progress False = return ()


{-
let display_tick = fun () -> print_now "."

displayTick :: IO ()
displayTick =
  let icona = [| "|"; "/" ; "-"; "\\" |] in
  let n     = ref 0                      in
  let pos   = ref 0                      in
  fun () ->
    let k   = !pos                       in
    let _   = pos := (k + 1) mod 4       in
    let _   = incr n                     in
    let suf = if (!n mod 76) = 0
              then "\n"
              else icona.(k)             in
    let _   = print_now ("\b."^suf)      in
    ()

-}
