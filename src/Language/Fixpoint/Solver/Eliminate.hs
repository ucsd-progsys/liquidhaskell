module Language.Fixpoint.Solver.Eliminate
       (eliminateAll, solve) where

import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Solver.Deps as D
import qualified Language.Fixpoint.Visitor     as V

import qualified Data.HashMap.Strict           as M


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

instance Elimable Pred where
  elimKVar kv pr p@(PKVar k su) | kv == k   = subst su pr
                                | otherwise = p
  elimKVar kv pr (PAnd ps)      = PAnd $ map (elimKVar kv pr) ps
  elimKVar kv pr (POr ps)       = POr  $ map (elimKVar kv pr) ps
  elimKVar kv pr (PNot p)       = PNot (elimKVar kv pr p)
  elimKVar kv pr (PImp p q)     = PImp (elimKVar kv pr p) (elimKVar kv pr q)
  elimKVar kv pr (PIff p q)     = PIff (elimKVar kv pr p) (elimKVar kv pr q)
  elimKVar kv pr (PAll bs p)    = PAll   bs (elimKVar kv pr p)
  elimKVar kv pr (PExist bs p)  = PExist bs (elimKVar kv pr p)
  elimKVar _ _ p                = p

instance Elimable (SubC a) where
  elimKVar kv pr x = x { sgrd = elimKVar kv pr (sgrd x)
                       , slhs = elimKVar kv pr (slhs x)
                       --, srhs = elimKVar kv pr (srhs x)
                       }

instance Elimable SortedReft where
  elimKVar kv pr x = x { sr_reft = elimKVar kv pr (sr_reft x) }

instance Elimable Reft where
  elimKVar kv pr (Reft (s, refa)) = Reft (s, (elimKVar kv pr refa))

instance Elimable Refa where
  elimKVar kv pr x = x { raPred = elimKVar kv pr (raPred x) }

instance Elimable (FInfo a) where
  elimKVar kv pr x = x { cm = M.map (elimKVar kv pr) (cm x)
                       , bs = elimKVar kv pr (bs x)
                       }

instance Elimable BindEnv where
  elimKVar kv pr benv = mapBindEnv (\(sym, sr) -> (sym, (elimKVar kv pr sr))) benv


eliminateAll :: FInfo a -> D.Deps -> FInfo a
eliminateAll fInfo ds = foldl eliminate fInfo (D.depNonCuts ds)

eliminate :: FInfo a -> KVar -> FInfo a
eliminate fInfo kv = elimKVar kv orPred (fInfo { cm = remainingSubCs })
  where
    relevantSubCs  = M.filter (\subC ->       kv `elem` (D.rhsKVars subC)) (cm fInfo)
    remainingSubCs = M.filter (\subC -> not $ kv `elem` (D.rhsKVars subC)) (cm fInfo)
    orPred = POr (map (foo kv fInfo) (M.elems relevantSubCs))

--TODO: ignores a constraint's sgrd, stag, and sinfo
--Assume we are given the kvar corresponding to the constraint's RHS
foo :: KVar -> FInfo a -> SubC a -> Pred
foo kv fInfo subC = pr'
  where
    bindings = envCs (bs fInfo) (senv subC)
    pr = predAndSimpleEnvFromEnvAndLhs bindings (slhs subC)
    (_, pr') = projectNonWFVars (bar (ws fInfo) kv) pr --TODO: remove unused retval

--TODO: ignores the WfC's env. also assumes will find exactly one wfc for a given kvar
bar :: [WfC a] -> KVar -> [(Symbol,Sort)]
bar wfcs kv = [(sym, sort)]
  where
    srefts = map wrft wfcs
    sreft = head [sreft | sreft <- srefts, elem kv (V.reftKVars (sr_reft sreft))]
    sym = reftBind $ sr_reft sreft
    sort = sr_sort sreft

projectNonWFVars :: [(Symbol,Sort)] -> ([(Symbol,Sort)],Pred) -> ([(Symbol,Sort)],Pred)
projectNonWFVars wfVars (vars, pr) = (vars', pr')
  where
    vars' = [var | var <- vars, elem var wfVars]
    pr' = PExist [var | var <- vars, not (elem var wfVars)] pr

-- [ x : {v : int | v = 10}
-- , y : {v : int | v = 20} ]
-- lhs {v : int | v = x}
-- ->
-- [v:int, x:int, y:int], (x = 10) /\ (y = 20) /\ (v = x)
predAndSimpleEnvFromEnvAndLhs :: [(Symbol, SortedReft)] -> SortedReft -> ([(Symbol,Sort)],Pred)
predAndSimpleEnvFromEnvAndLhs bindings lhs = baz $ (reftBind $ sr_reft lhs, lhs) : bindings

-- [ x : {v : int | v = 10}
-- , y : {v : int | v = 20} ]
-- ->
-- [x:int, y:int], (x = 10) /\ (y = 20)
baz :: [(Symbol, SortedReft)] -> ([(Symbol,Sort)],Pred)
baz bindings = (bs, pr)
  where
    bs = map (\(sym, sreft) -> (sym, sr_sort sreft)) bindings
    pr = PAnd $ map blah bindings

-- x : {v : int | v = 10}
-- ->
-- (x = 10)
blah :: (Symbol, SortedReft) -> Pred
blah (sym, sr) = subst1 (reftPred reft) sub
  where
    reft = sr_reft sr
    sub = ((reftBind reft), (eVar sym))


{-
data FInfo a = FI { cm    :: M.HashMap Integer (SubC a)
                  , ws    :: ![WfC a]
                  , bs    :: !BindEnv
                  , gs    :: !FEnv
                  , lits  :: ![(Symbol, Sort)]
                  ...
                  }

data SubC a = SubC { srhs  :: !SortedReft
                     ...
                   }

data Expr = ESym !SymConst
          | ECon !Constant
          | EVar !Symbol
          | ELit !LocSymbol !Sort
          | EApp !LocSymbol ![Expr]
          | ENeg !Expr
          | EBin !Bop !Expr !Expr
          | EIte !Pred !Expr !Expr
          | ECst !Expr !Sort
          | EBot
-}
