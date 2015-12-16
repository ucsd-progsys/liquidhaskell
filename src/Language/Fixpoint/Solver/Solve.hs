{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}

-- | Solve a system of horn-clause constraints ----------------------------

module Language.Fixpoint.Solver.Solve (solve) where

import           Control.Concurrent (threadDelay)
import           Control.Monad (filterM)
import           Control.Monad.State.Strict (lift)
import qualified Data.HashMap.Strict  as M
import           Language.Fixpoint.Utils.Progress
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types.Errors as F
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Config hiding (stats)
import qualified Language.Fixpoint.Solver.Solution as S
import qualified Language.Fixpoint.Solver.Worklist as W
import           Language.Fixpoint.Solver.Monad
-- DEBUG
import           Text.Printf
import           Debug.Trace
import           System.Console.CmdArgs.Verbosity (whenLoud)
import           Control.DeepSeq

---------------------------------------------------------------------------
solve :: (NFData a, F.Fixpoint a) => Config -> S.Solution -> F.SInfo a -> IO (F.Result a)
---------------------------------------------------------------------------
solve cfg s0 fi = do
    -- donePhase Loud "Worklist Initialize"
    (res, stat) <- runSolverM cfg fi n act
    whenLoud $ printStats fi wkl stat
    -- print (numIter stat)
    return res
  where
    wkl  = W.init fi
    n    = fromIntegral $ W.wRanks wkl
    act  = solve_ fi s0 wkl

printStats :: F.SInfo a ->  W.Worklist a -> Stats -> IO ()
printStats fi w s = putStrLn "\n" >> ppTs [ ptable fi, ptable s, ptable w ]
  where
    ppTs          = putStrLn . showpp . mconcat


---------------------------------------------------------------------------
solve_ :: (NFData a, F.Fixpoint a) => F.SInfo a -> S.Solution -> W.Worklist a -> SolveM (F.Result a, Stats)
---------------------------------------------------------------------------
solve_ fi s0 wkl = do
  let s0' = mappend s0 $ {-# SCC "sol-init" #-} S.init fi
  s   <- {-# SCC "sol-refine" #-} refine s0' wkl
  -- donePhase' "Solution: Fixpoint"
  st  <- stats
  res <- {-# SCC "sol-result" #-} result wkl s
  -- donePhase' "Solution: Check"
  return $!! (res, st)


---------------------------------------------------------------------------
refine :: S.Solution -> W.Worklist a -> SolveM S.Solution
---------------------------------------------------------------------------
refine s w
  | Just (c, w', newScc) <- W.pop w = do
     i       <- tickIter newScc
     (b, s') <- refineC i s c
     lift $ writeLoud $ refineMsg i c b
     let w'' = if b then W.push c w' else w'
     refine s' w''
  | otherwise = return s

-- DEBUG
refineMsg i c b = printf "\niter=%d id=%d change=%s\n"
                    i (F.subcId c) (show b)

---------------------------------------------------------------------------
-- | Single Step Refinement -----------------------------------------------
---------------------------------------------------------------------------
refineC :: Int -> S.Solution -> F.SimpC a -> SolveM (Bool, S.Solution)
---------------------------------------------------------------------------
refineC _i s c
  | null rhs  = return (False, s)
  | otherwise = do lhs   <- lhsPred  s c <$> getBinds
                   kqs   <- filterValid lhs rhs
                   return $ S.update s ks {- tracepp (msg ks rhs kqs) -} kqs
  where
    (ks, rhs) = rhsCands s c
    -- msg ks xs ys = printf "refineC: iter = %d, ks = %s, rhs = %d, rhs' = %d \n" _i (showpp ks) (length xs) (length ys)

lhsPred :: S.Solution -> F.SimpC a -> F.BindEnv -> F.Pred
lhsPred s c be = F.pAnd pBinds
  where
    pBinds     = S.apply s <$> xts
    xts        = F.envCs be $  F.senv c

rhsCands :: S.Solution -> F.SimpC a -> ([F.KVar], S.Cand (F.KVar, S.EQual))
rhsCands s c   = (fst <$> ks, kqs)
  where
    kqs        = [ cnd k su q | (k, su) <- ks, q <- S.lookup s k]
    ks         = predKs . F.crhs $ c
    cnd k su q = (F.subst su (S.eqPred q), (k, q))

predKs :: F.Pred -> [(F.KVar, F.Subst)]
predKs (F.PAnd ps)    = concatMap predKs ps
predKs (F.PKVar k su) = [(k, su)]
predKs _              = []

---------------------------------------------------------------------------
-- | Convert Solution into Result -----------------------------------------
---------------------------------------------------------------------------
result :: (F.Fixpoint a) => W.Worklist a -> S.Solution -> SolveM (F.Result a)
---------------------------------------------------------------------------
result wkl s = do
  let sol  = M.map (F.pAnd . fmap S.eqPred) s
  stat    <- result_ wkl s
  return   $ F.Result (F.sinfo <$> stat) sol

result_ :: W.Worklist a -> S.Solution -> SolveM (F.FixResult (F.SimpC a))
result_  w s   = res <$> filterM isUnsat' cs
  where
    cs         = W.unsatCandidates w
    res []     = F.Safe
    res cs'    = F.Unsafe cs'
    isUnsat' c = lift progressTick >> isUnsat s c

---------------------------------------------------------------------------
isUnsat :: S.Solution -> F.SimpC a -> SolveM Bool
---------------------------------------------------------------------------
isUnsat s c = do
  lp    <- lhsPred s c <$> getBinds
  let rp = rhsPred s c
  not   <$> isValid lp rp

isValid :: F.Pred -> F.Pred -> SolveM Bool
isValid p q = (not . null) <$> filterValid p [(q, ())]

rhsPred :: S.Solution -> F.SimpC a -> F.Pred
rhsPred s c = S.apply s $ F.crhs c

---------------------------------------------------------------------------
donePhase' :: String -> SolveM ()
---------------------------------------------------------------------------
donePhase' msg = lift $ do
  threadDelay 25000
  putBlankLn
  donePhase Loud msg
