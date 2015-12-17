{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE BangPatterns         #-}

module Language.Fixpoint.Solver.Eliminate
       (eliminateAll) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Names     (existSymbol)
import           Language.Fixpoint.Types.Visitor   (kvars)
import           Language.Fixpoint.Solver.Deps     (depNonCuts, deps)
import           Language.Fixpoint.Misc            (fst3)
import           Language.Fixpoint.Solver.Solution (Solution, mkJVar)

import qualified Data.HashMap.Strict as M
import           Data.List           (foldl')
import           Control.Arrow       (first, second)
import           Control.DeepSeq     (($!!))


--------------------------------------------------------------
eliminateAll :: SInfo a -> (Solution, SInfo a)
eliminateAll !fi = {-# SCC "eliminateAll" #-} foldl' eliminate (M.empty, fi) nonCuts
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
extractPred kDom be sc = renameQuantified (subcId sc) kSol
  where
    env = clhs be sc
    binds = second sr_sort <$> env
    nonFuncBinds = filter (nonFunction be . fst) binds
    lhsPreds = bindPred <$> env
    suPreds = substPreds kDom $ crhs sc
    kSol = PExist nonFuncBinds $ PAnd (lhsPreds ++ suPreds)

-- x:{v:int|v=10} -> (x=10)
bindPred :: (Symbol, SortedReft) -> Pred
bindPred (sym, sr) = subst1 (reftPred rft) sub
  where
    rft = sr_reft sr
    sub = (reftBind rft, eVar sym)

-- k0[v:=e1][x:=e2] -> [v = e1, x = e2]
substPreds :: [Symbol] -> Pred -> [Pred]
substPreds dom (PKVar _ (Su subs)) = [PAtom Eq (eVar sym) e | (sym, e) <- M.toList subs , sym `elem` dom]

nonFunction :: BindEnv -> Symbol -> Bool
nonFunction be sym = sym `notElem` funcs
  where
    funcs = [sym | (_, sym, sr) <- bindEnvToList be, isFunctionSortedReft sr]

domain :: BindEnv -> WfC a -> [Symbol]
domain be wfc = (fst3 $ wrft wfc) : map fst (envCs be $ wenv wfc)

renameQuantified :: Integer -> Pred -> Pred
renameQuantified i (PExist bs p) = PExist bs' p'
  where
    su  = substFromQBinds i bs
    bs' = (first $ subst su) <$> bs
    p'  = subst su p

substFromQBinds :: Integer -> [(Symbol, Sort)] -> Subst
substFromQBinds i bs = Su $ M.fromList [(s, EVar $ existSymbol s i) | s <- fst <$> bs]
