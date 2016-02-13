{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE BangPatterns         #-}

module Language.Fixpoint.Solver.Eliminate (eliminateAll) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Visitor   (kvars)
import           Language.Fixpoint.Partition       (depNonCuts, deps)
import           Language.Fixpoint.Misc            (fst3, errorstar)
import           Language.Fixpoint.Solver.Solution (Solution, mkJVar)

import qualified Data.HashMap.Strict as M
import           Data.List           (foldl')
import           Control.Arrow       (first, second)
import           Control.DeepSeq     (($!!))


--------------------------------------------------------------------------------
eliminateAll :: SInfo a -> (Solution, SInfo a)
eliminateAll !si = {-# SCC "eliminateAll" #-} foldl' eliminate (M.empty, si) nonCuts
  where
    nonCuts = depNonCuts $ deps si
--------------------------------------------------------------------------------
eliminate :: (Solution, SInfo a) -> KVar -> (Solution, SInfo a)
eliminate (!s, !fi) k = (M.insert k (mkJVar orPred) s, fi')
  where
    fi'    = fi { cm = nokCs , ws = M.delete k $ ws fi }
    kCs    = M.filter (   elem k . kvars . crhs) (cm fi) -- with    k in RHS (SLOW!)
    nokCs  = M.filter (notElem k . kvars . crhs) (cm fi) -- without k in RHS (SLOW!)
    kW     = (ws fi) M.! k
    kDom   = domain (bs fi) kW
    orPred = {-# SCC "orPred" #-} POr $!! extractPred kDom (bs fi)  <$> M.elems kCs

extractPred :: [Symbol] -> BindEnv -> SimpC a -> Expr
extractPred kDom be sc = renameQuantified (subcId sc) kSol
  where
    kSol               = PExist xts $ PAnd (lhsPreds ++ suPreds)
    xts                = filter (nonFunction be . fst) yts
    yts                = second sr_sort <$> env
    env                = clhs be sc
    lhsPreds           = bindPred <$> env
    suPreds            = substPreds kDom $ crhs sc

-- x:{v:int|v=10} -> (x=10)
bindPred :: (Symbol, SortedReft) -> Expr
bindPred (x, sr) = p `subst1`(v, eVar x)
  where
    v            = reftBind r
    r            = sr_reft sr
    p            = reftPred r

-- k0[v:=e1][x:=e2] -> [v = e1, x = e2]
substPreds :: [Symbol] -> Expr -> [Expr]
substPreds dom (PKVar _ (Su subs)) = [PAtom Eq (eVar x) e | (x, e) <- M.toList subs , x `elem` dom]
substPreds _ _ = errorstar "Eliminate.substPreds called on bad input"

-- SLOW!
nonFunction :: BindEnv -> Symbol -> Bool
nonFunction be sym = sym `notElem` funcs
  where
    funcs = [x | (_, x, sr) <- bindEnvToList be
               , isFunctionSortedReft sr]

domain :: BindEnv -> WfC a -> [Symbol]
domain be wfc = fst3 (wrft wfc) : map fst (envCs be $ wenv wfc)

renameQuantified :: Integer -> Expr -> Expr
renameQuantified i (PExist bs p) = PExist bs' p'
  where
    su  = substFromQBinds i bs
    bs' = first (subst su) <$> bs
    p'  = subst su p
renameQuantified _ _ = errorstar "Eliminate.renameQuantified called on bad input"

substFromQBinds :: Integer -> [(Symbol, Sort)] -> Subst
substFromQBinds i bs = Su $ M.fromList [(s, EVar $ existSymbol s i) | s <- fst <$> bs]
