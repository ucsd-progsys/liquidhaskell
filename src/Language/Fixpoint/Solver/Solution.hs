{-# LANGUAGE PatternGuards #-}
module Language.Fixpoint.Solver.Solution
        ( -- * Solutions and Results
          Solution

          -- * Initial Solution
        , init
        )
where


import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import           Data.Maybe                     (isNothing, fromMaybe)
import           Language.Fixpoint.Config
import           Language.Fixpoint.Solver.Monad
import           Language.Fixpoint.Sort
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types        as F
import           Prelude                        hiding (init)

---------------------------------------------------------------------------
-- | Types ----------------------------------------------------------------
---------------------------------------------------------------------------
type Solution = Sol KBind
type Sol a    = M.HashMap F.Symbol a
type KBind    = [EQual]


---------------------------------------------------------------------------
-- | Expanded or Instantiated Qualifier -----------------------------------
---------------------------------------------------------------------------

data EQual = EQ { eqQual :: !F.Qualifier
                , eqPred :: !F.Pred
                , eqArgs :: ![F.Expr]
                }
               deriving (Eq, Ord, Show)

{-@ data EQual = EQ { eqQual :: F.Qualifier
                    , eqPred :: F.Pred
                    , eqArgs :: {v: [F.Expr] | len v = len (q_params eqQual)}
                    }
  @-}

---------------------------------------------------------------------------
-- | Create Initial Solution from Qualifiers and WF constraints
---------------------------------------------------------------------------
init :: Config -> F.FInfo a -> Solution
---------------------------------------------------------------------------
init _ fi = L.foldl' (refine fi qs) s0 ws
  where
    s0    = M.empty
    qs    = F.quals fi
    ws    = F.ws    fi

refine :: F.FInfo a -> [F.Qualifier] -> Solution -> F.WfC a -> Solution
refine fi qs s w   = refineK (wfEnv fi w) qs s (wfKvar w)

refineK env qs s (v, t, k) = M.insert k eqs' s
  where
    eqs' = case M.lookup k s of
             Nothing  -> instK env v t k qs
             Just eqs -> [eq | eq <- eqs, okInst env v t eq]

instK :: F.SEnv F.SortedReft -> F.Symbol -> F.Sort -> F.Symbol -> [F.Qualifier] -> [EQual]
instK env v t k = concatMap (instKQ env v t k)

instKQ :: F.SEnv F.SortedReft -> F.Symbol -> F.Sort -> F.Symbol -> F.Qualifier -> [EQual]
instKQ env v t k q = error "TODO"

{-

  (qv, qt) : qvts = params q

  bind0 = t1 t2 t3 t4    s1 s2 s3 s4

  match :: [(Symbol, Sort)] -> [(Symbol, Sort)] -> [[Expr]]
  match xts (vt : yts) = do
    (th0, y0) <- candidates [(v,t)] qt
    es        <- go th0 [Var y0] yts
    return     $ reverse es

    where
      go th es ((y,t) : yts)
        = do (th', x) <- candidates xts t
             let th'' = th <> th'
             let yts' = [(y, apply th t) | (y, t) <- yts]
             go xts th'' (Var x : es) yts'
      go th es []
        = return es


   1. generate ALL xts combinations
   2. for each combination, instantiate,
   3.   check SORT if ok then return it.
-}

wfKvar :: F.WfC a -> (F.Symbol, F.Sort, F.Symbol)
wfKvar w@(F.WfC {F.wrft = sr})
  | F.Reft (v, F.Refa (F.PKVar k su)) <- F.sr_reft sr
  , F.isEmptySubst su = (v, F.sr_sort sr, k)
  | otherwise         = errorstar $ "wfKvar: malformed wfC " ++ show w

wfEnv :: F.FInfo a -> F.WfC a -> F.SEnv F.SortedReft
wfEnv fi w  = F.fromListSEnv xts
  where
    wbinds  = F.elemsIBindEnv $ F.wenv w
    bm      = F.bs fi
    xts     = [ F.lookupBindEnv i bm | i <- wbinds]

okInst :: F.SEnv F.SortedReft -> F.Symbol -> F.Sort -> EQual -> Bool
okInst env v t eq = isNothing $ checkSortedReftFull env sr
  where
    sr            = F.RR t (F.Reft (v, F.Refa (eqPred eq)))
