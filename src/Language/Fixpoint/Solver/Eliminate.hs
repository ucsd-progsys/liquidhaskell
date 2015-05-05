module Language.Fixpoint.Solver.Eliminate
       (eliminateAll, solve) where

import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Solver.Deps as D
import           Language.Fixpoint.Visitor (kvars, mapKVars)
import           Language.Fixpoint.Names   (nonSymbol, existSymbol)
import           Language.Fixpoint.Misc    (errorstar)

import qualified Data.HashMap.Strict           as M
import           Data.List (partition, (\\))
import           Data.Foldable (foldlM)
import           Control.Monad.State


--------------------------------------------------------------
-- | Dummy just for debugging --------------------------------
--------------------------------------------------------------
import qualified Text.PrettyPrint.HughesPJ as Debug
import           Language.Fixpoint.Config hiding (eliminate)
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


-- NOTE: assumes that eliminateAll is called only once for a given constraints file.
--       if not, starting the fresh-variable counter again at 0 is bad
eliminateAll :: FInfo a -> D.Deps -> FInfo a
eliminateAll fInfo ds = evalState (foldlM eliminate fInfo (D.depNonCuts ds)) 0

eliminate :: FInfo a -> KVar -> State Integer (FInfo a)
eliminate fInfo kv = do
  n <- get
  let relevantSubCs  = M.filter (      (elem kv) . D.rhsKVars) (cm fInfo)
  let remainingSubCs = M.filter (not . (elem kv) . D.rhsKVars) (cm fInfo)
  let (kvWfC, remainingWs) = findWfC kv (ws fInfo)
  let (bindingsList, (n', orPred)) = runState (mapM (extractPred kvWfC (bs fInfo)) (M.elems relevantSubCs)) (n, POr [])
  let bindings = concat bindingsList

  let be = bs fInfo
  let (ids, be') = insertsBindEnv [(sym, trueSortedReft srt) | (sym, srt) <- bindings] be
  let newSubCs = M.map (\s -> s { senv = insertsIBindEnv ids (senv s)}) remainingSubCs
  put n'
  return $ elimKVar kv orPred (fInfo { cm = newSubCs , ws = remainingWs , bs = be' })

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

extractPred :: WfC a -> BindEnv -> SubC a -> State (Integer, Pred) [(Symbol, Sort)]
extractPred wfc be subC = do (n, p@(POr preds)) <- get
                             let (bs, (n', pr')) = runState (mapM renameVar vars) (n, PAnd $ pr : [(blah (kVarVV, slhs subC))])
                             put (n', POr $ pr' : preds)
                             return bs
  where
    wfcIBinds  = elemsIBindEnv $ wenv wfc
    subcIBinds = elemsIBindEnv $ senv subC
    unmatchedIBinds | wfcIBinds `subset` subcIBinds = subcIBinds \\ wfcIBinds
                    | otherwise = errorstar $ "kVar is not well formed (missing bindings)"
    unmatchedIBindEnv = insertsIBindEnv unmatchedIBinds emptyIBindEnv
    unmatchedBindings = envCs be unmatchedIBindEnv

    kvSreft = wrft wfc
    kVarVV = reftBind $ sr_reft kvSreft

    (vars, pr) = baz unmatchedBindings


renameVar :: (Symbol, Sort) -> State (Integer, Pred) (Symbol, Sort)
renameVar (sym, srt) = do (n, pr) <- get
                          let sym' = existSymbol sym n
                          put ((n+1), subst1 pr (sym, eVar sym'))
                          return (sym', srt)

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
