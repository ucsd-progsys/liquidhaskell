{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Fixpoint.Solver.Eliminate
       (eliminateAll, findWfC) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Solver.Deps (depNonCuts, deps)
import           Language.Fixpoint.Visitor     (kvars, rhsKVars)
import           Language.Fixpoint.Names       (existSymbol)
import           Language.Fixpoint.Misc        (errorstar, snd3, thd3)
import           Language.Fixpoint.Solver.Solution (Solution, mkJVar)

import qualified Data.HashMap.Strict as M
import           Data.List           (partition, (\\))
import           Data.Foldable       (foldlM)
import           Control.Monad.State (get, put, runState, State, state)
import           Control.Arrow (second, (&&&))
import           Control.Applicative ((<$>))


data ElimState = ES { freshIdx :: Integer , solution :: Solution }

--------------------------------------------------------------
eliminateAll :: SInfo a -> (Solution, SInfo a)
eliminateAll fi = (s, fi')
  where
    nonCuts = depNonCuts $ deps fi
    (fi', ES n s) = runState (foldlM eliminate fi nonCuts) (ES 0 M.empty)
--------------------------------------------------------------

eliminate :: SInfo a -> KVar -> State ElimState (SInfo a)
eliminate fi kv = do
  let relevantSubCs  = M.filter (   elem kv . kvars . crhs) (cm fi)
  let remainingSubCs = M.filter (notElem kv . kvars . crhs) (cm fi)
  let (kvWfC, remainingWs) = findWfC kv (ws fi)
  predsBinds <- mapM (extractPred kvWfC (bs fi)) (M.elems relevantSubCs)
  let orPred = POr $ map fst predsBinds
  let symSReftList = map (second trueSortedReft) (concatMap snd predsBinds)
  let (ids, be) = insertsBindEnv symSReftList $ bs fi
  (ES n sol) <- get
  put (ES n (M.insert kv (mkJVar orPred) sol))
  return $ fi { cm = remainingSubCs , ws = remainingWs , bs = be }

insertsBindEnv :: [(Symbol, SortedReft)] -> BindEnv -> ([BindId], BindEnv)
insertsBindEnv = runState . mapM go
  where
    go (sym, srft) = do be <- get
                        let (id, be') = insertBindEnv sym srft be
                        put be'
                        return id
--insertsBindEnv = runState . mapM (uncurry $ (fmap.fmap) state insertBindEnv)

findWfC :: KVar -> [WfC a] -> (WfC a, [WfC a])
findWfC kv ws = (w', ws')
  where
    (w, ws') = partition (elem kv . kvars . sr_reft . wrft) ws
    w' | [x] <- w  = x
       | otherwise = errorstar $ show kv ++ " needs exactly one wf constraint"

extractPred :: WfC a -> BindEnv -> SimpC a -> State ElimState (Pred, [(Symbol, Sort)])
extractPred wfc be subC =  exprsToPreds . unzip <$> mapM renameVar vars
  where
    exprsToPreds (bs, subs) = (subst (mkSubst subs) finalPred, bs)
    wfcIBinds  = elemsIBindEnv $ wenv wfc
    subcIBinds = elemsIBindEnv $ senv subC
    unmatchedIBinds = subcIBinds \\ wfcIBinds
    unmatchedIBindEnv = insertsIBindEnv unmatchedIBinds emptyIBindEnv
    unmatchedBindings = envCs be unmatchedIBindEnv
    (vars, prList) = substBinds unmatchedBindings

    suPreds = substPreds (usableDomain be wfc) $ crhs subC
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


renameVar :: (Symbol, Sort) -> State ElimState ((Symbol, Sort), (Symbol, Expr))
renameVar (sym, srt) = do (ES n sol) <- get
                          let s = existSymbol sym n
                          put (ES (n+1) sol)
                          return ((s, srt) , (sym, eVar s))
--renameVar (sym, srt) = state $ (addExpr . existSymbol sym) &&& (+1)
--  where addExpr s = ((s, srt) , (sym, eVar s))

-- [ x:{v:int|v=10} , y:{v:int|v=20} ] -> [x:int, y:int], [(x=10), (y=20)]
substBinds :: [(Symbol, SortedReft)] -> ([(Symbol,Sort)],[Pred])
substBinds = unzip . map substBind

substBind :: (Symbol, SortedReft) -> ((Symbol,Sort), Pred)
substBind (sym, sr) = ((sym, sr_sort sr), subst1 (reftPred reft) sub)
  where
    reft = sr_reft sr
    sub = (reftBind reft, eVar sym)
