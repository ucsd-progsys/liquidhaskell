{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}

-- | Solve a system of horn-clause constraints ----------------------------

module Language.Fixpoint.Solver.Solve (solve) where

import           Control.Monad (filterM)
import           Control.Applicative ((<$>))
import qualified Data.HashMap.Strict  as M
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Config
import qualified Language.Fixpoint.Solver.Solution as S
import qualified Language.Fixpoint.Solver.Worklist as W
import           Language.Fixpoint.Solver.Monad

---------------------------------------------------------------------------
-- | The output of the Solver
---------------------------------------------------------------------------
type Result a = (F.FixResult (F.SubC a), M.HashMap F.KVar F.Pred)
---------------------------------------------------------------------------

---------------------------------------------------------------------------
solve :: Config -> F.FInfo a -> IO (Result a)
---------------------------------------------------------------------------
solve cfg fi = runSolverM $ solve_ cfg fi

---------------------------------------------------------------------------
solve_ :: Config -> F.FInfo a -> SolveM (Result a)
---------------------------------------------------------------------------
solve_ cfg fi = refine s0 wkl >>= solutionResult fi
  where
    s0        = S.init cfg fi
    wkl       = W.init cfg fi

---------------------------------------------------------------------------
refine :: S.Solution -> W.Worklist a -> SolveM S.Solution
---------------------------------------------------------------------------
refine s w
  | Just (c, w') <- W.pop w = do (b, s') <- refineC s c
                                 if b then refine s' (W.push c w')
                                      else return s'
  | otherwise               = return s


---------------------------------------------------------------------------
-- | Single Step Refinement -----------------------------------------------
---------------------------------------------------------------------------
refineC :: S.Solution -> F.SubC a -> SolveM (Bool, S.Solution)
---------------------------------------------------------------------------
refineC s c = do
  (env, lhs) <-  lhsPred  s c <$> getBinds
  let rhs     =  rhsCands s c
  S.update s <$> filterValid env lhs rhs

lhsPred :: S.Solution -> F.SubC a -> F.BindEnv -> (F.FEnv, F.Pred)
lhsPred s c be = (env, lhs)
  where
    env      = F.fromListSEnv xts
    lhs      = F.pAnd $ pGrd : pLhs : pBinds
    pGrd     = F.sgrd c
    pLhs     = S.apply s  $  F.lhsCs c
    pBinds   = S.apply s <$> xts
    xts      = F.envCs be $  F.senv c

rhsCands :: S.Solution -> F.SubC a -> S.Cand (F.KVar, S.EQual)
rhsCands s c   = [ cnd k su q | (k, su) <- ks c, q <- S.lookup s k]
  where
    ks         = predKs . F.reftPred . F.rhsCs
    cnd k su q = (F.subst su (S.eqPred q), (k, q))

predKs :: F.Pred -> [(F.KVar, F.Subst)]
predKs (F.PAnd ps)    = concatMap predKs ps
predKs (F.PKVar k su) = [(k, su)]
predKs _              = []

---------------------------------------------------------------------------
-- | Convert Solution into Result -----------------------------------------
---------------------------------------------------------------------------
solutionResult :: F.FInfo a -> S.Solution -> SolveM (Result a)
---------------------------------------------------------------------------
solutionResult fi s = (, sol) <$> result fi s
  where
    sol             = M.map (F.pAnd . fmap S.eqPred) s

result :: F.FInfo a -> S.Solution -> SolveM (F.FixResult (F.SubC a))
result fi s = res <$> filterM (isSat s) cs
  where
    cs      = M.elems $ F.cm fi
    res []  = F.Safe
    res cs' = F.Unsafe cs'

---------------------------------------------------------------------------
isSat :: S.Solution -> F.SubC a -> SolveM Bool
---------------------------------------------------------------------------
isSat s c = do
  (env, lp) <- lhsPred s c <$> getBinds
  let rp     = rhsPred s c
  isValid env lp rp

isValid :: F.FEnv -> F.Pred -> F.Pred -> SolveM Bool
isValid env p q = (not . null) <$> filterValid env p [(q, ())]

rhsPred :: S.Solution -> F.SubC a -> F.Pred
rhsPred s c = S.apply s $ F.rhsCs c
