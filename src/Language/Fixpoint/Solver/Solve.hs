{-# LANGUAGE PatternGuards #-}

-- | Solve a system of horn-clause constraints ----------------------------

module Language.Fixpoint.Solver.Solve (solve) where

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
type Result a = (F.FixResult (F.SubC a), M.HashMap F.Symbol F.Pred)
---------------------------------------------------------------------------

---------------------------------------------------------------------------
solve :: Config -> F.FInfo a -> IO (Result a)
---------------------------------------------------------------------------
solve cfg fi = runSolverM $ solve_ cfg fi

---------------------------------------------------------------------------
solve_ :: Config -> F.FInfo a -> SolveM (Result a)
---------------------------------------------------------------------------
solve_ cfg fi = refine fi s0 wkl >>= solutionResult fi
  where
    s0        = S.init cfg fi
    wkl       = W.init cfg fi

---------------------------------------------------------------------------
refine :: F.FInfo a -> S.Solution -> W.Worklist a -> SolveM S.Solution
---------------------------------------------------------------------------
refine fi s w
  | Just (c, w') <- W.pop w = do (b, s') <- refineC fi s c
                                 if b then refine fi s' (W.push c w')
                                      else return s'
  | otherwise               = return s


---------------------------------------------------------------------------
-- | Single Step Refinement -----------------------------------------------
---------------------------------------------------------------------------
refineC :: F.FInfo a -> S.Solution -> F.SubC a -> SolveM (Bool, S.Solution)
---------------------------------------------------------------------------
refineC fi s c = S.update s <$> filterValid lhs rhs
  where
    lhs        = lhsPred  fi s c
    rhs        = rhsCands    s c

lhsPred :: F.FInfo a -> S.Solution -> F.SubC a -> F.Pred
lhsPred fi s c = F.pAnd $ pLhs : pGrd : pBinds
  where
    pGrd       = F.sgrd c
    pLhs       = S.apply s  $  F.lhsCs    c
    pBinds     = S.apply s <$> F.envCs be c
    be         = F.bs fi

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
solutionResult = error "TODO"



