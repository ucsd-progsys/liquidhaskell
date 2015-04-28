module Language.Fixpoint.Solver.Eliminate
       (eliminateAll, solve) where

import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Solver.Deps as D
import           Language.Fixpoint.Visitor (kvars, mapKVars)
import           Language.Fixpoint.Names   (nonSymbol)
import           Language.Fixpoint.Misc    (errorstar)

import qualified Data.HashMap.Strict           as M
import           Data.List (partition)


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
  elimKVar kv pr x = x { sgrd = mapKVars go (sgrd x)
                       , slhs = elimKVar kv pr (slhs x)
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
eliminate fInfo kv = elimKVar kv orPred (fInfo { cm = remainingSubCs , ws = remainingWs})
  where
    relevantSubCs  = M.filter (      (elem kv) . D.rhsKVars) (cm fInfo)
    remainingSubCs = M.filter (not . (elem kv) . D.rhsKVars) (cm fInfo)
    (kvWfC, remainingWs) = bar kv (ws fInfo)
    orPred = POr (map (foo kvWfC fInfo) (M.elems relevantSubCs))

bar :: KVar -> [WfC a] -> (WfC a, [WfC a])
bar kv ws = (w', ws')
  where
    (w, ws') = partition (elem kv . kvars . sr_reft . wrft) ws
    w' | [x] <- w  = x
       | otherwise = errorstar $ (show kv) ++ " needs exactly one wf constraint"

--TODO: ignores a constraint's sgrd, stag, and sinfo
foo :: WfC a -> FInfo a -> SubC a -> Pred
foo wfc fInfo subC = pr'
  where
    kvSreft = wrft wfc
    bindings = envCs (bs fInfo) (senv subC)
    kVarVV = reftBind $ sr_reft kvSreft
    pr = baz $ (zoink kVarVV (slhs subC)) : bindings
    pr' = projectNonWFVars ((kVarVV, sr_sort kvSreft) : envBinds wfc fInfo) pr

projectNonWFVars :: [(Symbol,Sort)] -> ([(Symbol,Sort)],Pred) -> Pred
projectNonWFVars wfVars (vars, pr) = PExist [v | v <- vars, not (elem v wfVars)] pr

zoink :: Symbol -> SortedReft -> (Symbol, SortedReft)
zoink sym lhs = (sym, subst1 lhs (oldV, eVar sym))
  where
    oldV = reftBind $ sr_reft lhs

-- [ x:{v:int|v=10} , y:{v:int|v=20} ] -> [x:int, y:int], (x=10) /\ (y=20)
baz :: [(Symbol, SortedReft)] -> ([(Symbol,Sort)],Pred)
baz bindings = (bs, PAnd $ map blah bindings)
  where
    bs = map (\(sym, sreft) -> (sym, sr_sort sreft)) bindings

blah :: (Symbol, SortedReft) -> Pred
blah (sym, sr) = subst1 (reftPred reft) sub
  where
    reft = sr_reft sr
    sub = ((reftBind reft), (eVar sym))

envBinds :: WfC a -> FInfo a -> [(Symbol, Sort)]
envBinds w f = traceFix "hi" [(sym, sr_sort srft) | (sym, srft) <- envCs (bs f) (wenv w)]
