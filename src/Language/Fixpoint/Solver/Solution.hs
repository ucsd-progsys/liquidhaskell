{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}

module Language.Fixpoint.Solver.Solution
        ( -- * Solutions and Results
          Solution, Cand, EQual (..)

          -- * Types with Template/KVars
        , Solvable (..)

          -- * Initial Solution
        , init

          -- * Update Solutio n
        , update

          -- * Lookup Solution
        , lookup

          -- * RJ: What does this do ?
        , mkJVar
        )
where

import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)
import           Control.Parallel.Strategies
import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import           Data.Maybe                     (maybeToList, isNothing)
import           Data.Monoid                    ((<>))
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.SortCheck    as So
import           Language.Fixpoint.Utils.Misc
import qualified Language.Fixpoint.Types        as F
import           Prelude                        hiding (init, lookup)

---------------------------------------------------------------------
-- | Types ----------------------------------------------------------
---------------------------------------------------------------------

type Solution = Sol KBind
type Sol a    = M.HashMap F.KVar a
type KBind    = [EQual]
type Cand a   = [(F.Pred, a)]


---------------------------------------------------------------------
-- | Lookup Solution at KVar ----------------------------------------
---------------------------------------------------------------------
lookup :: Solution -> F.KVar -> KBind
---------------------------------------------------------------------
lookup s k = M.lookupDefault [] k s


---------------------------------------------------------------------
-- | Expanded or Instantiated Qualifier -----------------------------
---------------------------------------------------------------------

dummyQual = F.Q F.nonSymbol [] F.PFalse (F.dummyPos "")

mkJVar :: F.Pred -> KBind
mkJVar p = [EQL dummyQual p []]

data EQual = EQL { eqQual :: !F.Qualifier
                 , eqPred :: !F.Pred
                 , eqArgs :: ![F.Expr]
                 }
             deriving (Eq, Show, Data, Typeable, Generic)

instance PPrint EQual where
  pprint = pprint . eqPred

instance NFData EQual
--  where
  -- rnf (EQL q p _) = rnf q `seq` rnf p

{- EQL :: q:_ -> p:_ -> ListX F.Expr {q_params q} -> _ @-}

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
init :: F.SInfo a -> Solution
--------------------------------------------------------------------
init fi  = M.fromList keqs
  where
    keqs = map (refine fi qs) ws `using` parList rdeepseq
    qs   = F.quals fi
    ws   = M.elems $ F.ws fi


--------------------------------------------------------------------
refine :: F.SInfo a
       -> [F.Qualifier]
       -> F.WfC a
       -> (F.KVar, KBind)
--------------------------------------------------------------------
refine fi qs w = refineK env qs $ F.wrft w
  where
    env        = wenv <> genv
    wenv       = F.sr_sort <$> (F.fromListSEnv $ F.envCs (F.bs fi) (F.wenv w))
    genv       = F.lits fi

refineK :: F.SEnv F.Sort -> [F.Qualifier] -> (F.Symbol, F.Sort, F.KVar) -> (F.KVar, KBind)
refineK env qs (v, t, k) = (k, eqs')
   where
    eqs                  = instK env v t qs
    eqs'                 = filter (okInst env v t) eqs
    -- msg                  = "refineK: " ++ show k

--------------------------------------------------------------------
instK :: F.SEnv F.Sort
      -> F.Symbol
      -> F.Sort
      -> [F.Qualifier]
      -> [EQual]
--------------------------------------------------------------------
instK env v t = unique . concatMap (instKQ env v t)
  where
    unique = L.nubBy ((. eqPred) . (==) . eqPred)

instKQ :: F.SEnv F.Sort
       -> F.Symbol
       -> F.Sort
       -> F.Qualifier
       -> [EQual]
instKQ env v t q
  = do (su0, v0) <- candidates [(t, [v])] qt
       xs        <- match tyss [v0] (So.apply su0 <$> qts)
       return     $ eQual q (reverse xs)
    where
       qt : qts   = snd <$> F.q_params q
       tyss       = instCands env

instCands :: F.SEnv F.Sort -> [(F.Sort, [F.Symbol])]
instCands env = filter isOk tyss
  where
    tyss      = groupList [(t, x) | (x, t) <- xts]
    isOk      = isNothing . F.functionSort . fst
    xts       = F.toListSEnv env

match :: [(F.Sort, [F.Symbol])] -> [F.Symbol] -> [F.Sort] -> [[F.Symbol]]
match tyss xs (t : ts)
  = do (su, x) <- candidates tyss t
       match tyss (x : xs) (So.apply su <$> ts)
match _   xs []
  = return xs

-----------------------------------------------------------------------
candidates :: [(F.Sort, [F.Symbol])] -> F.Sort -> [(So.TVSubst, F.Symbol)]
-----------------------------------------------------------------------
candidates tyss tx
  = [(su, y) | (t, ys) <- tyss
             , su      <- maybeToList $ So.unifyFast mono tx t
             , y       <- ys                                   ]
  where
    mono = So.isMono tx

-----------------------------------------------------------------------
okInst :: F.SEnv F.Sort -> F.Symbol -> F.Sort -> EQual -> Bool
-----------------------------------------------------------------------
okInst env v t eq = isNothing tc
  where
    sr            = F.RR t (F.Reft (v, p))
    p             = eqPred eq
    tc            = {- tracepp msg $ -} So.checkSorted env sr
    msg           = "okInst [p := " ++ show p ++ " ]"

---------------------------------------------------------------------
-- | Apply Solution -------------------------------------------------
---------------------------------------------------------------------

class Solvable a where
  apply :: Solution -> a -> F.Pred

instance Solvable EQual where
  apply s = apply s . eqPred
  --TODO: this used to be just eqPred, but Eliminate allows KVars to
  -- have other KVars in their solutions. Does this extra 'apply s'
  -- make a significant difference?

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
