{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE PatternGuards      #-}

module Language.Fixpoint.Solver.Solution
        ( -- * Create and Update Solution
          init, update

          -- * Lookup Solution
        , lhsPred
        , noKvars

          -- * Debug
        , solutionGraph
        )
where

import           Control.Parallel.Strategies
import           Control.Arrow (second)
import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import           Data.Maybe                     (maybeToList, isNothing)
import           Data.Monoid                    ((<>))
import           Language.Fixpoint.Types.PrettyPrint ()
import           Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.SortCheck          as So
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types              as F
import           Language.Fixpoint.Types.Constraints hiding (ws, bs)
import           Language.Fixpoint.Types.Graphs
import           Prelude                        hiding (init, lookup)

-- DEBUG
-- import Text.Printf (printf)
-- import           Debug.Trace (trace)

--------------------------------------------------------------------------------
-- | Expanded or Instantiated Qualifier ----------------------------------------
--------------------------------------------------------------------------------

-- mkJVar :: F.Expr -> QBind
-- mkJVar p = [F.EQL dummyQual p []]

-- dummyQual :: F.Qualifier
-- dummyQual = F.Q F.nonSymbol [] F.PFalse (F.dummyPos "")

--------------------------------------------------------------------------------
-- | Update Solution -----------------------------------------------------------
--------------------------------------------------------------------------------
update :: Solution -> [F.KVar] -> [(F.KVar, F.EQual)] -> (Bool, Solution)
-------------------------------------------------------------------------
update s ks kqs = {- tracepp msg -} (or bs, s')
  where
    kqss        = groupKs ks kqs
    (bs, s')    = folds update1 s kqss
    -- msg         = printf "ks = %s, s = %s" (showpp ks) (showpp s)

folds   :: (a -> b -> (c, a)) -> a -> [b] -> ([c], a)
folds f b = L.foldl' step ([], b)
  where
     step (cs, acc) x = (c:cs, x')
       where
         (c, x')      = f acc x

groupKs :: [F.KVar] -> [(F.KVar, F.EQual)] -> [(F.KVar, QBind)]
groupKs ks kqs = M.toList $ groupBase m0 kqs
  where
    m0         = M.fromList $ (,[]) <$> ks

update1 :: Solution -> (F.KVar, QBind) -> (Bool, Solution)
update1 s (k, qs) = (change, solInsert k qs s)
  where
    oldQs         = solLookup s k
    change        = length oldQs /= length qs

--------------------------------------------------------------------
-- | Initial Solution (from Qualifiers and WF constraints) ---------
--------------------------------------------------------------------
init :: F.SInfo a -> Solution
--------------------------------------------------------------------
init si  = F.solFromList keqs [] -- (fromList keqs) M.empty
  where
    keqs = map (refine si qs) ws `using` parList rdeepseq
    qs   = F.quals si
    ws   = M.elems $ F.ws si

--------------------------------------------------------------------
refine :: F.SInfo a
       -> [F.Qualifier]
       -> F.WfC a
       -> (F.KVar, QBind)
--------------------------------------------------------------------
refine fi qs w = refineK env qs $ F.wrft w
  where
    env        = wenv <> genv
    wenv       = F.sr_sort <$> F.fromListSEnv (F.envCs (F.bs fi) (F.wenv w))
    genv       = F.lits fi

refineK :: F.SEnv F.Sort -> [F.Qualifier] -> (F.Symbol, F.Sort, F.KVar) -> (F.KVar, QBind)
refineK env qs (v, t, k) = {- tracepp msg -} (k, eqs')
   where
    eqs                  = instK env v t qs
    eqs'                 = filter (okInst env v t) eqs
    -- msg                  = printf "refineK: k = %s, eqs = %s" (showpp k) (showpp eqs)

--------------------------------------------------------------------
instK :: F.SEnv F.Sort
      -> F.Symbol
      -> F.Sort
      -> [F.Qualifier]
      -> QBind
--------------------------------------------------------------------
instK env v t = unique . concatMap (instKQ env v t)
  where
    unique = L.nubBy ((. F.eqPred) . (==) . F.eqPred)

instKQ :: F.SEnv F.Sort
       -> F.Symbol
       -> F.Sort
       -> F.Qualifier
       -> QBind
instKQ env v t q
  = do (su0, v0) <- candidates senv [(t, [v])] qt
       xs        <- match senv tyss [v0] (So.apply su0 <$> qts)
       return     $ F.eQual q (reverse xs)
    where
       qt : qts   = snd <$> F.q_params q
       tyss       = instCands env
       senv       = (`F.lookupSEnvWithDistance` env)

instCands :: F.SEnv F.Sort -> [(F.Sort, [F.Symbol])]
instCands env = filter isOk tyss
  where
    tyss      = groupList [(t, x) | (x, t) <- xts]
    isOk      = isNothing . F.functionSort . fst
    xts       = F.toListSEnv env

match :: So.Env -> [(F.Sort, [F.Symbol])] -> [F.Symbol] -> [F.Sort] -> [[F.Symbol]]
match env tyss xs (t : ts)
  = do (su, x) <- candidates env tyss t
       match env tyss (x : xs) (So.apply su <$> ts)
match _   _   xs []
  = return xs

--------------------------------------------------------------------------------
candidates :: So.Env -> [(F.Sort, [F.Symbol])] -> F.Sort -> [(So.TVSubst, F.Symbol)]
--------------------------------------------------------------------------------
candidates env tyss tx
  = [(su, y) | (t, ys) <- tyss
             , su      <- maybeToList $ So.unifyFast mono env tx t
             , y       <- ys                                   ]
  where
    mono = So.isMono tx

-----------------------------------------------------------------------
okInst :: F.SEnv F.Sort -> F.Symbol -> F.Sort -> F.EQual -> Bool
-----------------------------------------------------------------------
okInst env v t eq = isNothing tc
  where
    sr            = F.RR t (F.Reft (v, p))
    p             = F.eqPred eq
    tc            = So.checkSorted env sr


--------------------------------------------------------------------------------
-- | Predicate corresponding to LHS of constraint in current solution
--------------------------------------------------------------------------------
lhsPred :: F.BindEnv -> F.Solution -> F.SimpC a -> F.Expr
--------------------------------------------------------------------------------
lhsPred be s c = {- F.tracepp msg $ -} apply g s bs
  where
    g          = (be, bs)
    bs         = F.senv c
    -- msg        = "LhsPred for id = " ++ show (sid c)

type CombinedEnv = (F.BindEnv, F.IBindEnv)

apply :: CombinedEnv -> Solution -> F.IBindEnv -> F.Expr
apply g s bs = F.pAnd (apply1 g s <$> F.elemsIBindEnv bs)

apply1 :: CombinedEnv -> Solution -> F.BindId -> F.Expr
apply1 g s i = {- F.tracepp msg $ -} F.pAnd $ applyExpr g s <$> bindExprs g i
   -- where
   --  msg   = "apply1 bind = " ++ show i

bindExprs :: CombinedEnv -> F.BindId -> [F.Expr]
bindExprs (be,_) i = [p `F.subst1` (v, F.eVar x) | F.Reft (v, p) <- rs ]
  where
    (x, sr)        = F.lookupBindEnv i be
    rs             = F.reftConjuncts $ F.sr_reft sr

applyExpr :: CombinedEnv -> Solution -> F.Expr -> F.Expr
applyExpr g s (F.PKVar k su) = applyKVar g s k su
applyExpr _ _ p              = p

applyKVar :: CombinedEnv -> Solution -> F.KVar -> F.Subst -> F.Expr
applyKVar g s k su
  | Just eqs <- M.lookup k (F.sMap s)
  = qBindPred su eqs
  | Just cs  <- M.lookup k (F.sHyp s)
  = hypPred g s su cs
  | otherwise
  = errorstar $ "Unknown kvar: " ++ show k

hypPred :: CombinedEnv -> Solution -> F.Subst -> F.Hyp  -> F.Expr
hypPred g s su = F.pOr . fmap (cubePred g s su)

cubePred :: CombinedEnv -> Solution -> F.Subst -> F.Cube -> F.Expr
cubePred g s su c = F.PExist xts' $ F.pAnd [p', equate su su']
  where
    xts'          = symSorts g bs'
    p'            = apply (addCEnv g bs) s bs'
    bs'           = delCEnv bs g
    F.Cube bs su' = c

addCEnv :: CombinedEnv -> F.IBindEnv -> CombinedEnv
addCEnv (be, bs) bs' = (be, F.unionIBindEnv bs bs')

delCEnv :: F.IBindEnv -> CombinedEnv -> F.IBindEnv
delCEnv bs (_, bs')  = F.diffIBindEnv bs bs'

symSorts :: CombinedEnv -> F.IBindEnv -> [(F.Symbol, F.Sort)]
symSorts (be, _) bs = second F.sr_sort <$> F.envCs be bs

equate :: F.Subst -> F.Subst -> F.Expr
equate su su' = F.pAnd [F.PAtom F.Eq e e' | (_, (e, e')) <- joinSubst su su' ]

joinSubst :: F.Subst -> F.Subst -> [(F.Symbol, (F.Expr, F.Expr))]
joinSubst (F.Su m1) (F.Su m2) = M.toList $ M.intersectionWith (,) m1 m2

noKvars :: F.Expr -> Bool
noKvars = null . V.kvars

--------------------------------------------------------------------------------
qBindPred :: F.Subst -> QBind -> F.Expr
--------------------------------------------------------------------------------
qBindPred su eqs = F.subst su $ F.pAnd $ F.eqPred <$> eqs


--------------------------------------------------------------------------------
solutionGraph :: Solution -> KVGraph
--------------------------------------------------------------------------------
solutionGraph s = [ (KVar k, KVar k, KVar <$> eqKvars eqs) | (k, eqs) <- kEqs ]
  where
     eqKvars    = sortNub . concatMap (V.kvars . F.eqPred)
     kEqs       = M.toList (F.sMap s)
