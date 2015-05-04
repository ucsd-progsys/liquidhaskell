module Language.Fixpoint.Solver.Eliminate
       (eliminateAll, solve) where

import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Solver.Deps as D
import           Language.Fixpoint.Visitor (kvars, mapKVars)
import           Language.Fixpoint.Names   (nonSymbol)
import           Language.Fixpoint.Misc    (errorstar)

import qualified Data.HashMap.Strict           as M
import           Data.List (partition, (\\))
import           Control.Monad.State


--------------------------------------------------------------
-- | Dummy just for debugging --------------------------------
--------------------------------------------------------------
import qualified Text.PrettyPrint.HughesPJ as Debug
import           Language.Fixpoint.Config
solve :: Config -> FInfo a -> IO (FixResult a)
--------------------------------------------------------------
solve cfg fi = do
  let d = D.deps fi
  let blah = toFixpoint (eliminateAll fi d)
  putStr (Debug.render blah)
  return Safe


class Elimable a where
  elimKVar :: KVar -> Pred -> a -> a

instance Elimable (SubC a) where
  elimKVar kv pr x = x { slhs = elimKVar kv pr (slhs x)
                       --, srhs = elimKVar kv pr (srhs x)
                       }
    where
      go k = if kv == k then Just pr else Nothing

instance Elimable SortedReft where
  elimKVar kv pr x = x { sr_reft = elimKVar kv pr (sr_reft x) }

instance Elimable Reft where
  elimKVar kv pr = mapKVars go
    where
      go k = if kv == k then Just pr else Nothing

instance Elimable (FInfo a) where
  elimKVar kv pr x = x { cm = M.map (elimKVar kv pr) (cm x)
                       , bs = elimKVar kv pr (bs x)
                       }

instance Elimable BindEnv where
  elimKVar kv pr = mapBindEnv (\(sym, sr) -> (sym, (elimKVar kv pr sr)))


eliminateAll :: FInfo a -> D.Deps -> FInfo a
eliminateAll fInfo ds = foldl eliminate fInfo (D.depNonCuts ds)

--TODO: ignores the WfC's env
eliminate :: FInfo a -> KVar -> FInfo a
eliminate fInfo kv = elimKVar kv orPred (fInfo { cm = newSubCs , ws = remainingWs , bs = be' })
  where
    relevantSubCs  = M.filter (      (elem kv) . D.rhsKVars) (cm fInfo)
    remainingSubCs = M.filter (not . (elem kv) . D.rhsKVars) (cm fInfo)
    (kvWfC, remainingWs) = findWfC kv (ws fInfo)
    predsAndBindings = map (extractPred kvWfC (bs fInfo)) (M.elems relevantSubCs)
    preds    = map fst predsAndBindings
    bindings = concatMap snd predsAndBindings
    orPred = POr preds

    be = bs fInfo
    (ids, be') = insertsBindEnv [(sym, trueSortedReft srt) | (sym, srt) <- bindings] be
    newSubCs = M.map (\s -> s { senv = insertsIBindEnv ids (senv s)}) remainingSubCs

insertsBindEnv :: [(Symbol, SortedReft)] -> BindEnv -> ([BindId], BindEnv)
insertsBindEnv bs = runState (mapM go bs)
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

extractPred :: WfC a -> BindEnv -> SubC a -> (Pred, [(Symbol, Sort)])
extractPred wfc be subC = (PAnd $ [(blah (kVarVV, slhs subC)) , pr], vars)
  where
    wfcIBinds  = elemsIBindEnv $ wenv wfc
    subcIBinds = elemsIBindEnv $ senv subC
    unmatchedIBinds | wfcIBinds `subset` subcIBinds = subcIBinds \\ wfcIBinds
                    | otherwise = errorstar $ "kVar is not well formed (missing bindings)"
    unmatchedIBindEnv = insertsIBindEnv unmatchedIBinds emptyIBindEnv
    unmatchedBindings = envCs be unmatchedIBindEnv

    kvSreft = wrft wfc
    kVarVV = reftBind $ sr_reft kvSreft

    (vars,pr) = baz $ unmatchedBindings


--trueSortedReft :: Sort -> SortedReft
--insertBindEnv :: Symbol -> SortedReft -> BindEnv -> (BindId, BindEnv)


subset :: (Eq a) => [a] -> [a] -> Bool
subset xs ys = (xs \\ ys) == []

-- [ x:{v:int|v=10} , y:{v:int|v=20} ] -> [x:int, y:int], (x=10) /\ (y=20)
baz :: [(Symbol, SortedReft)] -> ([(Symbol,Sort)],Pred)
baz bindings = (bs, PAnd $ map blah bindings)
  where
    bs = map (\(sym, sreft) -> (sym, sr_sort sreft)) bindings

-- [ x:{v:int|v=10} ] -> (x=10)
blah :: (Symbol, SortedReft) -> Pred
blah (sym, sr) = subst1 (reftPred reft) sub
  where
    reft = sr_reft sr
    sub = ((reftBind reft), (eVar sym))
