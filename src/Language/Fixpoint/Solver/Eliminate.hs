module Language.Fixpoint.Solver.Eliminate
       (eliminateAll) where

import qualified Language.Fixpoint.Types       as F
import qualified Language.Fixpoint.Solver.Deps as D
import qualified Language.Fixpoint.Visitor     as V

import qualified Data.HashMap.Strict           as M
import qualified Data.List                     as L


instance F.Subable (F.SubC a) where
  substa f                 = error "TODO"
  substf f x               = error "TODO"
  subst su x               = error "TODO"
  syms x                   = error "TODO"


eliminateAll :: F.FInfo a -> D.Deps -> F.FInfo a
eliminateAll = error "TODO"

eliminate :: F.FInfo a -> F.KVar -> F.FInfo a
eliminate fInfo kv = error "TODO"
  where
    (relevantSubCs, remainingSubCs) = L.partition (\subC -> kv `elem` (D.rhsKVars subC)) (M.elems (F.cm fInfo))
    orPred = F.POr (map (foo kv fInfo) relevantSubCs)

--TODO: ignores a constraint's sgrd, stag, and sinfo
--Assume we are given the kvar corresponding to the constraint's RHS
foo :: F.KVar -> F.FInfo a -> F.SubC a -> F.Pred
foo kv fInfo subC = pr'
  where
    bindings = F.envCs (F.bs fInfo) (F.senv subC)
    pr = predAndSimpleEnvFromEnvAndLhs bindings (F.slhs subC)
    (_, pr') = projectNonWFVars (bar (F.ws fInfo) kv) pr --TODO: remove unused retval

--TODO: ignores the WfC's env. also assumes will find exactly one wfc for a given kvar
bar :: [F.WfC a] -> F.KVar -> [(F.Symbol,F.Sort)]
bar wfcs kv = [(sym, sort)]
  where
    srefts = map F.wrft wfcs
    sreft = head [sreft | sreft <- srefts, elem kv (V.reftKVars (F.sr_reft sreft))]
    sym = F.reftBind $ F.sr_reft sreft
    sort = F.sr_sort sreft

projectNonWFVars :: [(F.Symbol,F.Sort)] -> ([(F.Symbol,F.Sort)],F.Pred) -> ([(F.Symbol,F.Sort)],F.Pred)
projectNonWFVars wfVars (vars, pr) = (vars', pr')
  where
    vars' = [var | var <- vars, elem var wfVars]
    pr' = F.PExist [var | var <- vars, not (elem var wfVars)] pr

-- [ x : {v : int | v = 10}
-- , y : {v : int | v = 20} ]
-- lhs {v : int | v = x}
-- ->
-- [v:int, x:int, y:int], (x = 10) /\ (y = 20) /\ (v = x)
predAndSimpleEnvFromEnvAndLhs :: [(F.Symbol, F.SortedReft)] -> F.SortedReft -> ([(F.Symbol,F.Sort)],F.Pred)
predAndSimpleEnvFromEnvAndLhs bindings lhs = baz $ (F.reftBind $ F.sr_reft lhs, lhs) : bindings

-- [ x : {v : int | v = 10}
-- , y : {v : int | v = 20} ]
-- ->
-- [x:int, y:int], (x = 10) /\ (y = 20)
baz :: [(F.Symbol, F.SortedReft)] -> ([(F.Symbol,F.Sort)],F.Pred)
baz bindings = (bs, pr)
  where
    bs = map (\(sym, sreft) -> (sym, F.sr_sort sreft)) bindings
    pr = F.PAnd $ map blah bindings

-- x : {v : int | v = 10}
-- ->
-- (x = 10)
blah :: (F.Symbol, F.SortedReft) -> F.Pred
blah (sym, sr) = F.subst1 (F.reftPred reft) sub
  where
    reft = F.sr_reft sr
    sub = ((F.reftBind reft), (F.eVar sym))


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
