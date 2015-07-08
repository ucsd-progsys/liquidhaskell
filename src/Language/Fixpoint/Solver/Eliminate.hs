{-# LANGUAGE PatternGuards    #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Fixpoint.Solver.Eliminate
       (eliminateAll, elimKVar, findWfC) where

import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Solver.Deps as D
import           Language.Fixpoint.Visitor (kvars, mapKVars)
import           Language.Fixpoint.Names   (existSymbol)
import           Language.Fixpoint.Misc    (errorstar)

import qualified Data.HashMap.Strict           as M
import           Data.List (partition, (\\))
import           Data.Foldable (foldlM)
import           Control.Monad.State (get, put, runState, evalState, State)


--------------------------------------------------------------
eliminateAll :: FInfo a -> FInfo a
eliminateAll fi = evalState (foldlM eliminate fi nonCuts) 0
  where
    nonCuts = D.depNonCuts $ D.deps fi
--------------------------------------------------------------


class Elimable a where
  elimKVar :: ((KVar, Subst) -> Maybe Pred) -> a -> a

instance Elimable (SubC a) where
  elimKVar f x = x { slhs = elimKVar f (slhs x) 
                   , srhs = elimKVar f (srhs x)
                   }

instance Elimable SortedReft where
  elimKVar f x = x { sr_reft = mapKVars f (sr_reft x) }

instance Elimable (FInfo a) where
  elimKVar f x = x { cm = M.map (elimKVar f) (cm x)
                   , bs = elimKVar f (bs x)
                   }

instance Elimable BindEnv where
  elimKVar f = mapBindEnv (\(sym, sr) -> (sym, elimKVar f sr))


eliminate :: FInfo a -> KVar -> State Integer (FInfo a)
eliminate fi kv = do
  let relevantSubCs  = M.filter (   elem kv . D.rhsKVars) (cm fi)
  let remainingSubCs = M.filter (notElem kv . D.rhsKVars) (cm fi)
  let (kvWfC, remainingWs) = findWfC kv (ws fi)
  foo <- mapM (extractPred kvWfC (bs fi)) (M.elems relevantSubCs)
  let orPred = POr $ map fst foo
  let symSrtList = concatMap snd foo
  let symSReftList = [(sym, trueSortedReft srt) | (sym, srt) <- symSrtList]
  let (ids, be) = insertsBindEnv symSReftList $ bs fi
  let newSubCs = M.map (\s -> s { senv = insertsIBindEnv ids (senv s)}) remainingSubCs
  let go (k, _) = if kv == k then Just orPred else Nothing
  return $ elimKVar go (fi { cm = newSubCs , ws = remainingWs , bs = be })

insertsBindEnv :: [(Symbol, SortedReft)] -> BindEnv -> ([BindId], BindEnv)
insertsBindEnv = runState . mapM go
  where
    go (sym, srft) = do be <- get
                        let (id, be') = insertBindEnv sym srft be
                        put be'
                        return id

findWfC :: KVar -> [WfC a] -> (WfC a, [WfC a])
findWfC kv ws = (w', ws')
  where
    (w, ws') = partition (elem kv . kvars . sr_reft . wrft) ws
    w' | [x] <- w  = x
       | otherwise = errorstar $ (show kv) ++ " needs exactly one wf constraint"

extractPred :: WfC a -> BindEnv -> SubC a -> State Integer (Pred, [(Symbol, Sort)])
extractPred wfc be subC = do foo <- mapM renameVar vars
                             let (bs, subs) = unzip foo
                             return (subst (mkSubst subs) finalPred, bs)
  where
    wfcIBinds  = elemsIBindEnv $ wenv wfc
    subcIBinds = elemsIBindEnv $ senv subC
    unmatchedIBinds = subcIBinds \\ wfcIBinds
    unmatchedIBindEnv = insertsIBindEnv unmatchedIBinds emptyIBindEnv
    unmatchedBindings = envCs be unmatchedIBindEnv
    lhs = slhs subC
    (vars, prList) = baz $ (reftBind $ sr_reft lhs, lhs) : unmatchedBindings

    suPreds = substPreds (domain be wfc) $ reftPred $ sr_reft $ srhs subC
    finalPred = PAnd $ prList ++ suPreds

-- on rhs, $k0[v:=e1][x:=e2] -> [v = e1, x = e2]
substPreds :: [Symbol] -> Pred -> [Pred]
substPreds dom (PKVar _ (Su subs)) = [PAtom Eq (eVar sym) expr | (sym, expr) <- subs , sym `elem` dom]

domain :: BindEnv -> WfC a -> [Symbol]
domain be wfc = (reftBind $ sr_reft $ wrft wfc) : (map fst $ envCs be $ wenv wfc)

renameVar :: (Symbol, Sort) -> State Integer ((Symbol, Sort), (Symbol, Expr))
renameVar (sym, srt) = do n <- get
                          let sym' = existSymbol sym n
                          put (n+1)
                          return ((sym', srt), (sym, eVar sym'))

-- [ x:{v:int|v=10} , y:{v:int|v=20} ] -> [x:int, y:int], [(x=10), (y=20)]
baz :: [(Symbol, SortedReft)] -> ([(Symbol,Sort)],[Pred])
baz = unzip . map blah

blah :: (Symbol, SortedReft) -> ((Symbol,Sort), Pred)
blah (sym, sr) = ((sym, sr_sort sr), subst1 (reftPred reft) sub)
  where
    reft = sr_reft sr
    sub = ((reftBind reft), (eVar sym))
