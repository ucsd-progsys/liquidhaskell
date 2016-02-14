{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TupleSections      #-}

module Language.Fixpoint.Solver.Solution
        ( -- * Solutions and Results
          Solution    -- RJ: DO NOT expose!
        , sMap
        , Cand

          -- * Eliminate
        , Hyp
        , Cube (..)

          -- * Types with Template/KVars
        , Solvable (..)

          -- * Initial Solution
        , empty
        , init

          -- * Access Solution
        , lookup
        , insert
        , update

          -- * Final result
        , result

          -- * RJ: What does this do ?
        , mkJVar

          -- * Debug
        , solutionGraph
          -- HIDEME
        , noKvars
        , apply1

        )
where

import           Control.Parallel.Strategies
import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import           Data.Maybe                     (maybeToList, isNothing)
import           Data.Monoid                    ((<>))
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.SortCheck    as So
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types        as F
import           Language.Fixpoint.Types       (Expr (..))
import           Language.Fixpoint.Types.Graphs
import           Prelude                        hiding (init, lookup)

-- DEBUG
-- import Text.Printf (printf)
-- import           Debug.Trace (trace)

--------------------------------------------------------------------------------
-- | Types ---------------------------------------------------------------------
--------------------------------------------------------------------------------

type Solution = Sol QBind

data Sol a = Sol { sMap :: M.HashMap F.KVar a
                 , sHyp :: M.HashMap F.KVar Hyp
                 }

data Cube = Cube
  { cuBinds :: [F.BindId]
  , cuSubst :: F.Subst
  }

type Hyp  = ListNE Cube

type QBind    = [F.EQual]

type Cand a   = [(F.Expr, a)]

instance Monoid (Sol a) where
  mempty        = Sol mempty mempty
  mappend s1 s2 = Sol { sMap = mappend (sMap s1) (sMap s2)
                      , sHyp = mappend (sHyp s1) (sHyp s2)
                      }

instance Functor Sol where
  fmap f (Sol s h) = Sol (f <$> s) h

instance PPrint a => PPrint (Sol a) where
  pprint = pprint . sMap

--------------------------------------------------------------------------------
result :: Solution -> M.HashMap F.KVar F.Expr
--------------------------------------------------------------------------------
result s = sMap $ (F.pAnd . fmap F.eqPred) <$> s

--------------------------------------------------------------------------------
-- | Read / Write Solution at KVar ---------------------------------------------
--------------------------------------------------------------------------------
lookup :: Solution -> F.KVar -> QBind
--------------------------------------------------------------------------------
lookup s k = M.lookupDefault [] k (sMap s)

--------------------------------------------------------------------------------
insert :: F.KVar -> a -> Sol a -> Sol a
--------------------------------------------------------------------------------
insert k qs s = s { sMap = M.insert k qs (sMap s) }


--------------------------------------------------------------------------------
-- | Expanded or Instantiated Qualifier ----------------------------------------
--------------------------------------------------------------------------------

mkJVar :: F.Expr -> QBind
mkJVar p = [F.EQL dummyQual p []]

dummyQual :: F.Qualifier
dummyQual = F.Q F.nonSymbol [] F.PFalse (F.dummyPos "")

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
update1 s (k, qs) = (change, insert k qs s)
  where
    oldQs         = lookup s k
    change        = length oldQs /= length qs

--------------------------------------------------------------------
-- | Initial Solution (from Qualifiers and WF constraints) ---------
--------------------------------------------------------------------
init :: F.SInfo a -> Solution
--------------------------------------------------------------------
init fi  = Sol (M.fromList keqs) M.empty
  where
    keqs = map (refine fi qs) ws `using` parList rdeepseq
    qs   = F.quals fi
    ws   = M.elems $ F.ws fi

--------------------------------------------------------------------
empty :: Solution
--------------------------------------------------------------------
empty  = Sol M.empty M.empty

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
-- | Apply Solution ------------------------------------------------------------
--------------------------------------------------------------------------------

class Solvable a where
  apply :: F.BindEnv -> F.IBindEnv -> Solution -> a -> F.Expr

-- instance Solvable EQual where
--   apply s = apply s . eqPred
  --TODO: this used to be just eqPred, but Eliminate allows KVars to
  -- have other KVars in their solutions. Does this extra 'apply s'
  -- make a significant difference?

-- instance Solvable F.KVar where
  -- apply s k = apply s $ safeLookup err k s
    -- where
      -- err   = "apply: Unknown KVar " ++ show k

instance Solvable (F.KVar, F.Subst) where
  apply _ _ s (k, su) = applyKvQual s k su
   --F.subst su (apply s $ {- tracepp msg -} k)
    -- where
      -- msg         = "apply-kvar: "

instance Solvable F.Expr where
  apply = applyExpr
  -- apply s = V.trans (V.defaultVisitor {V.txExpr = tx}) () ()
    -- where
      -- tx _ (F.PKVar k su) = apply s (k, su)
      -- tx _ p              = p

instance Solvable F.Reft where
  apply be g s = apply be g s . F.reftPred

instance Solvable F.SortedReft where
  apply be g s = apply be g s . F.sr_reft

instance Solvable (F.Symbol, F.SortedReft) where
  apply be g s (x, sr) = p `F.subst1` (v, F.eVar x)
    where
      p                = apply be g s r
      F.Reft (v, r)   = F.sr_reft sr

instance Solvable a => Solvable [a] where
  apply be g s = F.pAnd . fmap (apply be g s)

applyKvQual :: Solution -> F.KVar -> F.Subst -> F.Expr
applyKvQual s k su = qBindPred su eqs
  where
    eqs            = safeLookup err k (sMap s)
    err            = "applyKvQual: Unknown KVar " ++ show k

qBindPred :: F.Subst -> QBind -> F.Expr
qBindPred su eqs = F.subst su $ F.pAnd $ F.eqPred <$> eqs

applyExpr :: F.BindEnv -> F.IBindEnv -> Solution -> F.Expr -> F.Expr
applyExpr = error "TODO:HEREHEREHEREHERE"
-- applyExpr be g s e = error "TODO:HEREHEREHEREHERE" -- tracepp "applyExpr" $ go 0 e
  -- where
    -- go i e
     -- | noKvars e = e
     -- | otherwise = go (i+1) (apply1 s $ {- trace (msg i e) -} e)
    -- msg i e = "Depth: " ++ show i ++ "Size: " ++ show (V.size e)

noKvars :: F.Expr -> Bool
noKvars = null . V.kvars

apply1   :: Solution -> F.Expr -> F.Expr
apply1 s = go
  where
    go e                = go' e
    go' (PKVar k su)    = applyKvQual s k su
    go' e@(ESym _)      = e
    go' e@(ECon _)      = e
    go' e@(EVar _)      = e
    go' e@PGrad         = e
    go' (EApp f e)      = EApp    (go f)  (go e)
    go' (ENeg e)        = ENeg    (go e)
    go' (EBin o e1 e2)  = EBin o  (go e1) (go e2)
    go' (EIte p e1 e2)  = EIte    (go  p) (go e1) (go e2)
    go' (ECst e t)      = ECst    (go e) t
    go' (PAnd  ps)      = PAnd    (go <$> ps)
    go' (POr  ps)       = POr     (go <$> ps)
    go' (PNot p)        = PNot    (go p)
    go' (PImp p1 p2)    = PImp    (go p1) (go p2)
    go' (PIff p1 p2)    = PIff    (go p1) (go p2)
    go' (PAtom r e1 e2) = PAtom r (go e1) (go e2)
    go' (PAll xts p)    = PAll xts (go p)
    go' (PExist xts p)  = PExist xts (go p)
    go' (ETApp e s)     = ETApp (go e) s
    go' (ETAbs e s)     = ETAbs (go e) s

--------------------------------------------------------------------------------

{-

solve g s bs = pAnd (solve1 g s <$> bs)

solve1 g s (F.PKVar k su) = solveK g s k su
solve1 g _ p              = p

solveK g s k su
  | Just eqs <- M.lookup k (sMap s)
  = qBindPred su eqs
  | Just cs  <- M.lookup k (hMap s)
  = hBindPred g s su cs
  | otherwise
  = panic $ "Unknown kvar: " ++ show k

hBindPred g s su = F.pOr . fmap (cubePred g s su)

cubePred g s su (Cube bs su') = exists xts' (pAnd [p', equate su su'])
  where
    xts' = symSort <$> bs'
    p'   = solve (g + bs) bs'
    bs'  = bs - g

 -}






--------------------------------------------------------------------------------
solutionGraph :: Solution -> KVGraph
solutionGraph s = [ (KVar k, KVar k, KVar <$> eqKvars eqs) | (k, eqs) <- kEqs ]
  where
     eqKvars    = sortNub . concatMap (V.kvars . F.eqPred)
     kEqs       = M.toList (sMap s)
