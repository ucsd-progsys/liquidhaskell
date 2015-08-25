{-# LANGUAGE PatternGuards    #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Fixpoint.Solver.Eliminate
       (eliminateAll, elimKVar, findWfC) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Solver.Deps (depNonCuts, deps)
import           Language.Fixpoint.Visitor     (kvars, mapKVars', rhsKVars)
import           Language.Fixpoint.Names       (existSymbol)
import           Language.Fixpoint.Misc        (errorstar, snd3, thd3)

import qualified Data.HashMap.Strict as M
import           Data.List           (partition, (\\))
import           Data.Foldable       (foldlM)
import           Control.Monad.State (get, put, runState, evalState, State, state)
import           Control.Arrow (second, (&&&))
import           Control.Applicative ((<$>))


--------------------------------------------------------------
eliminateAll :: FInfo a -> FInfo a
eliminateAll fi = evalState (foldlM eliminate fi nonCuts) 0
  where
    nonCuts = depNonCuts $ deps fi
--------------------------------------------------------------


class Elimable a where
  elimKVar :: ((KVar, Subst) -> Maybe Pred) -> a -> a

instance Elimable (SubC a) where
  elimKVar f x = x { slhs = elimKVar f (slhs x) 
                   , srhs = elimKVar f (srhs x)
                   }

instance Elimable SortedReft where
  elimKVar f x = x { sr_reft = mapKVars' f (sr_reft x) }

instance Elimable (FInfo a) where
  elimKVar f x = x { cm = M.map (elimKVar f) (cm x)
                   , bs = elimKVar f (bs x)
                   }

instance Elimable BindEnv where
  elimKVar f = mapBindEnv $ second (elimKVar f)


eliminate :: FInfo a -> KVar -> State Integer (FInfo a)
eliminate fi kv = do
  let relevantSubCs  = M.filter (   elem kv . rhsKVars) (cm fi)
  let remainingSubCs = M.filter (notElem kv . rhsKVars) (cm fi)
  let (kvWfC, remainingWs) = findWfC kv (ws fi)
  predsBinds <- mapM (extractPred kvWfC (bs fi)) (M.elems relevantSubCs)
  let orPred = POr $ map fst predsBinds
  let symSReftList = map (second trueSortedReft) (concatMap snd predsBinds)
  let (ids, be) = insertsBindEnv symSReftList $ bs fi
  let newSubCs = M.map (\s -> s { senv = insertsIBindEnv ids (senv s)}) remainingSubCs
  let replacement (k, _) = if kv == k then Just orPred else Nothing
  return $ elimKVar replacement (fi { cm = newSubCs , ws = remainingWs , bs = be })

insertsBindEnv :: [(Symbol, SortedReft)] -> BindEnv -> ([BindId], BindEnv)
insertsBindEnv = runState . mapM (uncurry $ (fmap.fmap) state insertBindEnv)

findWfC :: KVar -> [WfC a] -> (WfC a, [WfC a])
findWfC kv ws = (w', ws')
  where
    (w, ws') = partition (elem kv . kvars . sr_reft . wrft) ws
    w' | [x] <- w  = x
       | otherwise = errorstar $ show kv ++ " needs exactly one wf constraint"

extractPred :: WfC a -> BindEnv -> SubC a -> State Integer (Pred, [(Symbol, Sort)])
extractPred wfc be subC =  exprsToPreds . unzip <$> mapM renameVar vars
  where
    exprsToPreds (bs, subs) = (subst (mkSubst subs) finalPred, bs)
    wfcIBinds  = elemsIBindEnv $ wenv wfc
    subcIBinds = elemsIBindEnv $ senv subC
    unmatchedIBinds = subcIBinds \\ wfcIBinds
    unmatchedIBindEnv = insertsIBindEnv unmatchedIBinds emptyIBindEnv
    unmatchedBindings = envCs be unmatchedIBindEnv
    lhs = slhs subC
    (vars, prList) = substBinds $ (reftBind $ sr_reft lhs, lhs) : unmatchedBindings

    suPreds = substPreds (usableDomain be wfc) $ reftPred $ sr_reft $ srhs subC
    finalPred = PAnd $ prList ++ suPreds

-- on rhs, $k0[v:=e1][x:=e2] -> [v = e1, x = e2]
substPreds :: [Symbol] -> Pred -> [Pred]
substPreds dom (PKVar _ (Su subs)) = [PAtom Eq (eVar sym) expr | (sym, expr) <- subs , sym `elem` dom]

-- TODO: filtering out functions like this is a temporary hack - we shouldn't
-- have function substitutions to begin with
usableDomain :: BindEnv -> WfC a -> [Symbol]
usableDomain be wfc = filter nonFunction $ domain be wfc
  where
    nonFunction sym = sym `notElem` functionsInBindEnv be

domain :: BindEnv -> WfC a -> [Symbol]
domain be wfc = reftBind (sr_reft $ wrft wfc) : map fst (envCs be $ wenv wfc)

functionsInBindEnv :: BindEnv -> [Symbol]
functionsInBindEnv be = map snd3 fList
  where
    fList = filter (isFunctionSortedReft . thd3) $ bindEnvToList be


renameVar :: (Symbol, Sort) -> State Integer ((Symbol, Sort), (Symbol, Expr))
renameVar (sym, srt) = state $ (addExpr . existSymbol sym) &&& (+1)
  where addExpr s = ((s, srt) , (sym, eVar s))

-- [ x:{v:int|v=10} , y:{v:int|v=20} ] -> [x:int, y:int], [(x=10), (y=20)]
substBinds :: [(Symbol, SortedReft)] -> ([(Symbol,Sort)],[Pred])
substBinds = unzip . map substBind

substBind :: (Symbol, SortedReft) -> ((Symbol,Sort), Pred)
substBind (sym, sr) = ((sym, sr_sort sr), subst1 (reftPred reft) sub)
  where
    reft = sr_reft sr
    sub = (reftBind reft, eVar sym)
