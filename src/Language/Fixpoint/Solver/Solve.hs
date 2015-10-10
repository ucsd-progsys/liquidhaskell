{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}

-- | Solve a system of horn-clause constraints ----------------------------

module Language.Fixpoint.Solver.Solve (solve) where

import           Data.Monoid (mappend)
import           Control.Monad (filterM)
import           Control.Applicative ((<$>))
import           Control.Monad.State.Strict (lift)
import qualified Data.HashMap.Strict  as M
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Config
import qualified Language.Fixpoint.Solver.Solution as S
import qualified Language.Fixpoint.Solver.Worklist as W
import           Language.Fixpoint.Solver.Monad
import           Language.Fixpoint.Solver.Eliminate (eliminateAll)

-- DEBUG
import           Text.Printf
import           Language.Fixpoint.PrettyPrint
import           Debug.Trace
import           Text.PrettyPrint.HughesPJ          (render)


---------------------------------------------------------------------------
solve :: (F.Fixpoint a) => Config -> S.Solution -> F.SInfo a -> IO (F.Result a)
---------------------------------------------------------------------------
solve cfg s0 fi = runSolverM cfg fi (workListSize wkl) $ do
    lift $ donePhase Loud "Worklist Initialize"
    solve_ fi s0 wkl
  where
    wkl = W.init fi

workListSize :: W.Worklist -> Integer
workListSize _ = 100 -- FIXME: this should be #sccs

---------------------------------------------------------------------------
solve_ :: (F.Fixpoint a) => F.SInfo a -> S.Solution -> W.Worklist -> SolveM (F.Result a)
---------------------------------------------------------------------------
solve_ fi s0 wkl = do
  let s0' = mappend s0 $ S.init fi
  lift $ donePhase Loud "Solution Initialize"
  s <- refine s0' wkl
  lift $ donePhase Loud "Solution Fixpoint"
  result fi s

---------------------------------------------------------------------------
refine :: S.Solution -> W.Worklist a -> SolveM S.Solution
---------------------------------------------------------------------------
refine s w
  | Just (c, w', newScc) <- W.pop w = do
     i       <- tickIter newScc
     (b, s') <- refineC i s c
     lift $ writeLoud $ refineMsg i c b w
     let w'' = if b then W.push c w' else w'
     refine s' w''
  | otherwise = return s

-- DEBUG
refineMsg i c b w = printf "REFINE: iter = %d cid = %s change = %s wkl = %s"
                      i (show $ F.sid c) (show b) (showpp w)

---------------------------------------------------------------------------
-- | Single Step Refinement -----------------------------------------------
---------------------------------------------------------------------------
refineC :: Int -> S.Solution -> F.SimpC a -> SolveM (Bool, S.Solution)
---------------------------------------------------------------------------
refineC _i s c
  | null rhs  = return (False, s)
  | otherwise = do lhs   <- lhsPred  s c <$> getBinds
                   kqs   <- filterValid lhs rhs
                   return $ S.update s ks {-  $ tracepp (msg ks rhs kqs) -} kqs
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
result :: (F.Fixpoint a) => F.SInfo a -> S.Solution -> SolveM (F.Result a)
---------------------------------------------------------------------------
result fi s = do
  let sol  = M.map (F.pAnd . fmap S.eqPred) s
  stat    <- result_ fi s
  return   $ F.Result (F.WrapC <$> stat) sol

result_ :: F.SInfo a -> S.Solution -> SolveM (F.FixResult (F.SimpC a))
result_ fi s = res <$> filterM (isUnsat s) cs
  where
    cs       = M.elems $ F.cm fi
    res []   = F.Safe
    res cs'  = F.Unsafe cs'

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
