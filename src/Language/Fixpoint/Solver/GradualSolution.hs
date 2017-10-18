{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TupleSections      #-}

module Language.Fixpoint.Solver.GradualSolution
  ( -- * Create Initial Solution
    init
  ) where

import           Control.Parallel.Strategies
import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import           Data.Maybe                     (maybeToList, isNothing)
import           Data.Monoid                    ((<>))
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.PrettyPrint ()
import qualified Language.Fixpoint.SortCheck          as So
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types              as F
import qualified Language.Fixpoint.Types.Solutions    as Sol
import           Language.Fixpoint.Types.Constraints  hiding (ws, bs)
import           Prelude                              hiding (init, lookup)
import           Language.Fixpoint.Solver.Sanitize  (symbolEnv)
import Language.Fixpoint.SortCheck

--------------------------------------------------------------------------------
-- | Initial Gradual Solution (from Qualifiers and WF constraints) -------------
--------------------------------------------------------------------------------
init :: (F.Fixpoint a) => Config -> F.SInfo a -> [(F.KVar, (F.GWInfo, [F.Expr]))]
--------------------------------------------------------------------------------
init cfg si = map (elab . refineG si qs genv) gs `using` parList rdeepseq 
  where
    qs         = F.quals si
    gs         = snd <$> gs0
    genv       = instConstants si

    gs0        = L.filter (isGWfc . snd) $ M.toList (F.ws si)

    elab (k,(x,es)) = ((k,) . (x,)) $ (elaborate "init" (sEnv (gsym x) (gsort x)) <$> es)
    
    sEnv x s    = isEnv {F.seSort = F.insertSEnv x s (F.seSort isEnv)}
    isEnv       = symbolEnv cfg si


--------------------------------------------------------------------------------
refineG :: F.SInfo a -> [F.Qualifier] -> F.SEnv F.Sort -> F.WfC a -> (F.KVar, (F.GWInfo, [F.Expr]))
refineG fi qs genv w = (k, (F.gwInfo w, Sol.qbExprs qb))
  where 
    (k, qb) = refine fi qs genv w 

refine :: F.SInfo a -> [F.Qualifier] -> F.SEnv F.Sort -> F.WfC a -> (F.KVar, Sol.QBind)
refine fi qs genv w = refineK (allowHOquals fi) env qs $ F.wrft w
  where
    env             = wenv <> genv
    wenv            = F.sr_sort <$> F.fromListSEnv (F.envCs (F.bs fi) (F.wenv w))

instConstants :: F.SInfo a -> F.SEnv F.Sort
instConstants = F.fromListSEnv . filter notLit . F.toListSEnv . F.gLits
  where
    notLit    = not . F.isLitSymbol . fst


refineK :: Bool -> F.SEnv F.Sort -> [F.Qualifier] -> (F.Symbol, F.Sort, F.KVar) -> (F.KVar, Sol.QBind)
refineK ho env qs (v, t, k) = (k, eqs')
   where
    eqs                     = instK ho env v t qs
    eqs'                    = Sol.qbFilter (okInst env v t) eqs

--------------------------------------------------------------------------------
instK :: Bool
      -> F.SEnv F.Sort
      -> F.Symbol
      -> F.Sort
      -> [F.Qualifier]
      -> Sol.QBind
--------------------------------------------------------------------------------
instK ho env v t = Sol.qb . unique . concatMap (instKQ ho env v t)
  where
    unique       = L.nubBy ((. Sol.eqPred) . (==) . Sol.eqPred)

instKQ :: Bool
       -> F.SEnv F.Sort
       -> F.Symbol
       -> F.Sort
       -> F.Qualifier
       -> [Sol.EQual]
instKQ ho env v t q
  = do (su0, v0) <- candidates senv [(t, [v])] qt
       xs        <- match senv tyss [v0] (So.apply su0 <$> qts)
       return     $ Sol.eQual q (reverse xs)
    where
       qt : qts   = snd <$> F.qParams q
       tyss       = instCands ho env
       senv       = (`F.lookupSEnvWithDistance` env)

instCands :: Bool -> F.SEnv F.Sort -> [(F.Sort, [F.Symbol])]
instCands ho env = filter isOk tyss
  where
    tyss      = groupList [(t, x) | (x, t) <- xts]
    isOk      = if ho then const True else isNothing . F.functionSort . fst
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
candidates env tyss tx = 
    [(su, y) | (t, ys) <- tyss
             , su      <- maybeToList $ So.unifyFast mono env tx t
             , y       <- ys                                   ]
  where
    mono = So.isMono tx

--------------------------------------------------------------------------------
okInst :: F.SEnv F.Sort -> F.Symbol -> F.Sort -> Sol.EQual -> Bool
--------------------------------------------------------------------------------
okInst env v t eq = isNothing tc
  where
    sr            = F.RR t (F.Reft (v, p))
    p             = Sol.eqPred eq
    tc            = So.checkSorted env sr 


