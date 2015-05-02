{-# LANGUAGE PatternGuards     #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}

module Language.Fixpoint.Solver.Solution
        ( -- * Solutions and Results
          Solution, Cand, EQual (..)

          -- * Types with Template/KVars
        , Solvable (..)

          -- * Initial Solution
        , init

          -- * Update Solution
        , update

          -- * Lookup Solution
        , lookup
        )
where

import           Control.Applicative            ((<$>))
import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import           Data.Maybe                     (maybeToList, isNothing) -- , fromMaybe)
import           Language.Fixpoint.PrettyPrint
import           Language.Fixpoint.Config
import           Language.Fixpoint.Visitor      as V
import qualified Language.Fixpoint.Sort         as So
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types        as F
import           Prelude                        hiding (init, lookup)

---------------------------------------------------------------------
-- | Types ----------------------------------------------------------
---------------------------------------------------------------------

type Solution = Sol KBind
type Sol a    = M.HashMap F.KVar a
type KBind    = [EQual]
type Cand a   = [(F.Pred, a)]

lookup :: Solution -> F.KVar -> KBind
lookup s k = M.lookupDefault [] k s

---------------------------------------------------------------------
-- | Expanded or Instantiated Qualifier -----------------------------
---------------------------------------------------------------------

data EQual = EQL { eqQual :: !F.Qualifier
                 , eqPred :: !F.Pred
                 , eqArgs :: ![F.Expr]
                 }
             deriving (Eq, Ord, Show)

instance PPrint EQual where
  pprint = pprint . eqPred

{-@ EQL :: q:_ -> p:_ -> ListX F.Expr {q_params q} -> _ @-}

eQual :: F.Qualifier -> [F.Symbol] -> EQual
eQual q xs = EQL q p es
  where
    p      = F.subst su $  F.q_body q
    su     = F.mkSubst  $  safeZip "eQual" qxs es
    es     = F.eVar    <$> xs
    qxs    = fst       <$> F.q_params q

------------------------------------------------------------------------
-- | Update Solution ---------------------------------------------------
------------------------------------------------------------------------
update :: Solution -> [F.KVar] -> [(F.KVar, EQual)] -> (Bool, Solution)
-------------------------------------------------------------------------
update s ks kqs = {- traceShow msg -} (or bs, s')
  where
    kqss        = groupKs ks kqs
    (bs, s')    = folds update1 s kqss
    -- msg         = "s = " ++ showpp s

groupKs :: [F.KVar] -> [(F.KVar, EQual)] -> [(F.KVar, [EQual])]
groupKs ks kqs = M.toList $ groupBase m0 kqs
  where
    m0         = M.fromList $ (,[]) <$> ks

update1 :: Solution -> (F.KVar, KBind) -> (Bool, Solution)
update1 s (k, qs) = (change, M.insert k qs s)
  where
    oldQs         = lookup s k
    change        = length oldQs /= length qs


--------------------------------------------------------------------
-- | Initial Solution (from Qualifiers and WF constraints) ---------
--------------------------------------------------------------------
init :: Config -> F.FInfo a -> Solution
--------------------------------------------------------------------
init _ fi = traceShow "init solution"  s
  where
    s     = L.foldl' (refine fi qs) s0 ws
    s0    = M.empty
    qs    = F.quals fi
    ws    = F.ws    fi

--------------------------------------------------------------------
refine :: F.FInfo a
       -> [F.Qualifier]
       -> Solution
       -> F.WfC a
       -> Solution
--------------------------------------------------------------------
refine fi qs s w = refineK env qs s (wfKvar w)
  where
    env          = F.fromListSEnv $ F.envCs (F.bs fi) (F.wenv w)


refineK :: F.SEnv F.SortedReft
        -> [F.Qualifier]
        -> Solution
        -> (F.Symbol, F.Sort, F.KVar)
        -> Solution
refineK env qs s (v, t, k) = M.insert k eqs' s
  where
    eqs' = case M.lookup k s of
             Nothing  -> instK env v t qs
             Just eqs -> [eq | eq <- eqs, okInst env v t eq]

--------------------------------------------------------------------
instK :: F.SEnv F.SortedReft
      -> F.Symbol
      -> F.Sort
      -> [F.Qualifier]
      -> [EQual]
--------------------------------------------------------------------
instK env v t = unique . concatMap (instKQ env v t)
  where
    unique qs = M.elems $ M.fromList [(eqPred q, q) | q <- qs ]

instKQ :: F.SEnv F.SortedReft
       -> F.Symbol
       -> F.Sort
       -> F.Qualifier
       -> [EQual]
instKQ env v t q
  = do (su0, v0) <- candidates [(v, t)] qt
       xs        <- match xts [v0] (So.apply su0 <$> qts)
       return     $ eQual q (reverse xs)
    where
       qt : qts   = snd <$> F.q_params q
       xts        = F.toListSEnv (F.sr_sort <$> env)

match :: [(F.Symbol, F.Sort)] -> [F.Symbol] -> [F.Sort] -> [[F.Symbol]]
match xts xs (t : ts)
  = do (su, x) <- candidates xts t
       match xts (x : xs) (So.apply su <$> ts)
match _   xs []
  = return xs


-----------------------------------------------------------------------
candidates :: [(F.Symbol, F.Sort)] -> F.Sort -> [(So.TVSubst, F.Symbol)]
-----------------------------------------------------------------------
candidates xts t'
  = [(su, x) | (x, t) <- xts, su <- maybeToList $ So.unify t' t]

-----------------------------------------------------------------------
wfKvar :: F.WfC a -> (F.Symbol, F.Sort, F.Symbol)
-----------------------------------------------------------------------
wfKvar w@(F.WfC {F.wrft = sr})
  | F.Reft (v, F.Refa (F.PKVar k su)) <- F.sr_reft sr
  , F.isEmptySubst su = (v, F.sr_sort sr, k)
  | otherwise         = errorstar $ "wfKvar: malformed wfC " ++ show w

-----------------------------------------------------------------------
okInst :: F.SEnv F.SortedReft -> F.Symbol -> F.Sort -> EQual -> Bool
-----------------------------------------------------------------------
okInst env v t eq = isNothing $ So.checkSortedReftFull env sr
  where
    sr            = F.RR t (F.Reft (v, F.Refa (eqPred eq)))

---------------------------------------------------------------------
-- | Apply Solution -------------------------------------------------
---------------------------------------------------------------------

class Solvable a where
  apply :: Solution -> a -> F.Pred

instance Solvable EQual where
  apply _ = eqPred

instance Solvable F.KVar where
  apply s k = apply s $ safeLookup err k s
    where
      err   = "apply: Unknown KVar " ++ show k

instance Solvable (F.KVar, F.Subst) where
  apply s (k, su) = F.subst su (apply s k)

instance Solvable F.Pred where
  apply s = V.trans (V.defaultVisitor {V.txPred = tx}) () ()
    where
      tx _ (F.PKVar k su) = apply s (k, su)
      tx _ p              = p

instance Solvable F.Refa where
  apply s = apply s . F.raPred

instance Solvable F.Reft where
  apply s = apply s . F.reftPred

instance Solvable F.SortedReft where
  apply s = apply s . F.sr_reft

instance Solvable (F.Symbol, F.SortedReft) where
  apply s (x, sr)   = p `F.subst1` (v, F.eVar x)
    where
      p             = apply s r
      F.Reft (v, r) = F.sr_reft sr

instance Solvable a => Solvable [a] where
  apply s = F.pAnd . fmap (apply s)

