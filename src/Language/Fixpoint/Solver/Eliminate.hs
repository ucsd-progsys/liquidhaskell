{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE BangPatterns         #-}

module Language.Fixpoint.Solver.Eliminate
       (eliminateAll, findWfC) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Solver.Deps (depNonCuts, deps)
import           Language.Fixpoint.Visitor     (kvars, rhsKVars)
import           Language.Fixpoint.Names       (existSymbol)
import           Language.Fixpoint.Misc        (errorstar, snd3, thd3)
import           Language.Fixpoint.Solver.Solution (Solution, mkJVar)

import qualified Data.HashMap.Strict as M
import           Data.List           (partition, (\\), foldl')
import           Control.Monad.State (get, put, runState, evalState, State, state)
import           Control.Applicative ((<$>))
import           Control.Arrow       (second)
import           Control.DeepSeq     (($!!))


--------------------------------------------------------------
eliminateAll :: SInfo a -> (Solution, SInfo a)
eliminateAll !fi = foldl' eliminate (M.empty, fi) nonCuts
  where
    nonCuts = depNonCuts $ deps fi
--------------------------------------------------------------

eliminate :: (Solution, SInfo a) -> KVar -> (Solution, SInfo a)
eliminate (!s, !fi) kv = (M.insert kv (mkJVar orPred) s, fi { cm = remainingCs , ws = remainingWs})
  where
    relevantCs  = M.filter (   elem kv . kvars . crhs) (cm fi)
    remainingCs = M.filter (notElem kv . kvars . crhs) (cm fi)
    (kvWfC, remainingWs) = findWfC kv (ws fi)
    orPred = {-# SCC "orPred" #-} POr $!! extractPred kvWfC fi <$> M.elems relevantCs

findWfC :: KVar -> [WfC a] -> (WfC a, [WfC a])
findWfC kv ws = (w', ws')
  where
    (w, ws') = partition (elem kv . kvars . sr_reft . wrft) ws
    w' | [x] <- w  = x
       | otherwise = errorstar $ show kv ++ " needs exactly one wf constraint"

extractPred :: WfC a -> SInfo a -> SimpC a -> Pred
extractPred wfc fi sc = projectNonWFVars be binds wfc $ PAnd (lhsPreds ++ suPreds)
  where
    be = bs fi
    binds = second sr_sort <$> envCs be (senv sc)
    lhsPreds = bindPred <$> envCs be (senv sc)
    suPreds = substPreds (usableDomain be wfc) $ crhs sc

-- x:{v:int|v=10} -> (x=10)
bindPred :: (Symbol, SortedReft) -> Pred
bindPred (sym, sr) = subst1 (reftPred reft) sub
  where
    reft = sr_reft sr
    sub = (reftBind reft, eVar sym)

-- on rhs, $k0[v:=e1][x:=e2] -> [v = e1, x = e2]
substPreds :: [Symbol] -> Pred -> [Pred]
substPreds dom (PKVar _ (Su subs)) = [PAtom Eq (eVar sym) expr | (sym, expr) <- M.toList subs , sym `elem` dom]

-- TODO: filtering out functions like this is a temporary hack - we shouldn't
-- have function substitutions to begin with
usableDomain :: BindEnv -> WfC a -> [Symbol]
usableDomain be wfc = filter nonFunction $ domain be wfc
  where
    nonFunction sym = sym `notElem` functionsInBindEnv be

functionsInBindEnv :: BindEnv -> [Symbol]
functionsInBindEnv be = map snd3 fList
  where
    fList = filter (isFunctionSortedReft . thd3) $ bindEnvToList be

domain :: BindEnv -> WfC a -> [Symbol]
domain be wfc = reftBind (sr_reft $ wrft wfc) : map fst (envCs be $ wenv wfc)

projectNonWFVars :: BindEnv -> [(Symbol,Sort)] -> WfC a -> Pred -> Pred
projectNonWFVars be binds wf pr = PExist [v | v <- binds, not (elem (fst v) wfVars)] pr
  where
    wfVars = domain be wf
    

