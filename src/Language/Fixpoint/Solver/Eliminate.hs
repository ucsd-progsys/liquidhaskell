{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE BangPatterns         #-}

module Language.Fixpoint.Solver.Eliminate
       (eliminateAll) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Solver.Deps     (depNonCuts, deps)
import           Language.Fixpoint.Visitor         (kvars)
import           Language.Fixpoint.Misc            (errorstar, fst3)
import           Language.Fixpoint.Solver.Solution (Solution, mkJVar)

import qualified Data.HashMap.Strict as M
import           Data.List           (partition, foldl')
import           Control.Arrow       (second)
import           Control.DeepSeq     (($!!))


--------------------------------------------------------------
eliminateAll :: SInfo a -> (Solution, SInfo a)
eliminateAll !fi = foldl' eliminate (M.empty, fi) nonCuts
  where
    nonCuts = depNonCuts $ deps fi
--------------------------------------------------------------

eliminate :: (Solution, SInfo a) -> KVar -> (Solution, SInfo a)
eliminate (!s, !fi) k = (M.insert k (mkJVar orPred) s, fi { cm = remainingCs , ws = M.delete k $ ws fi })
  where
    relevantCs  = M.filter (   elem k . kvars . crhs) (cm fi)
    remainingCs = M.filter (notElem k . kvars . crhs) (cm fi)
    kvWfC = ws fi M.! k
    be = bs fi
    kDom = domain be kvWfC
    orPred = {-# SCC "orPred" #-} POr $!! extractPred kDom be <$> M.elems relevantCs

extractPred :: [Symbol] -> BindEnv -> SimpC a -> Pred
extractPred kDom be sc = projectNonWFVars binds kDom $ PAnd (lhsPreds ++ suPreds)
  where
    env = envCs be (senv sc)
    binds = second sr_sort <$> env
    lhsPreds = bindPred <$> env
    suPreds = substPreds (usableDomain be kDom) $ crhs sc

-- x:{v:int|v=10} -> (x=10)
bindPred :: (Symbol, SortedReft) -> Pred
bindPred (sym, sr) = subst1 (reftPred rft) sub
  where
    rft = sr_reft sr
    sub = (reftBind rft, eVar sym)

-- k0[v:=e1][x:=e2] -> [v = e1, x = e2]
substPreds :: [Symbol] -> Pred -> [Pred]
substPreds dom (PKVar _ (Su subs)) = [PAtom Eq (eVar sym) e | (sym, e) <- M.toList subs , sym `elem` dom]

-- TODO: filtering out functions like this is a temporary hack - we shouldn't
-- have function substitutions to begin with
usableDomain :: BindEnv -> [Symbol] -> [Symbol]
usableDomain be = filter nonFunction
  where
    nonFunction sym = sym `notElem` functionsInBindEnv be

functionsInBindEnv :: BindEnv -> [Symbol]
functionsInBindEnv be = [sym | (_, sym, sr) <- bindEnvToList be, isFunctionSortedReft sr]

domain :: BindEnv -> WfC a -> [Symbol]
domain be wfc = (sortedReftValueVariable $ wrft wfc) : map fst (envCs be $ wenv wfc)

sortedReftValueVariable (RR _ (Reft (v,_))) = v

projectNonWFVars :: [(Symbol,Sort)] -> [Symbol] -> Pred -> Pred
projectNonWFVars binds kDom pr = PExist [v | v <- binds, notElem (fst v) kDom] pr
