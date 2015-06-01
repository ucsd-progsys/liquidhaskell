-- | Validate and Transform Constraints to Ensure various Invariants -------------------------
--   1. Each binder must be unique

module Language.Fixpoint.Solver.Validate
       ( -- * Validate and Transform FInfo to enforce invariants
         validate

         -- * Sorts for each Symbol
       , symbolSorts
       )
       where

import           Language.Fixpoint.Visitor (foldSort)
import           Language.Fixpoint.Config
import           Language.Fixpoint.PrettyPrint
import qualified Language.Fixpoint.Misc   as Misc
import qualified Language.Fixpoint.Types  as F
import qualified Language.Fixpoint.Errors as E
import qualified Data.HashMap.Strict      as M
import qualified Data.List as L
-- import           Control.Monad (filterM)
-- import           Control.Applicative ((<$>))
--import           Debug.Trace (trace)
import           Text.Printf

---------------------------------------------------------------------------
validate :: Config -> F.FInfo a -> Either E.Error (F.FInfo a)
---------------------------------------------------------------------------
validate _ = Right . dropHigherOrderBinders . renameVV

---------------------------------------------------------------------------
-- | symbol |-> sort for EVERY variable in the FInfo
---------------------------------------------------------------------------
symbolSorts :: F.FInfo a -> Either E.Error [(F.Symbol, F.Sort)]
---------------------------------------------------------------------------
symbolSorts fi = compact . (\z -> lits ++ consts ++ z) =<< bindSorts fi
  where
    lits       = F.lits fi
    consts     = [(x, t) | (x, F.RR t _) <- F.toListSEnv $ F.gs fi]

compact :: [(F.Symbol, F.Sort)] -> Either E.Error [(F.Symbol, F.Sort)]
compact xts
  | null bad  = Right [(x, t) | (x, [t]) <- ok ]
  | otherwise = Left $ dupBindErrors bad
  where
    (bad, ok) = L.partition multiSorted . binds $ xts
    binds     = M.toList . M.map Misc.sortNub . Misc.group

---------------------------------------------------------------------------
bindSorts  :: F.FInfo a -> Either E.Error [(F.Symbol, F.Sort)]
---------------------------------------------------------------------------
bindSorts fi
  | null bad   = Right [ (x, t) | (x, [(t, _)]) <- ok ]
  | otherwise  = Left $ dupBindErrors [ (x, map fst ts) | (x, ts) <- bad]
  where
    (bad, ok)  = L.partition multiSorted . binds $ fi
    binds      = symBinds . F.bs

multiSorted :: (x, [t]) -> Bool
multiSorted = (1 <) . length . snd

dupBindErrors :: [(F.Symbol, [F.Sort])] -> E.Error
dupBindErrors = foldr1 E.catError . map dbe
  where
   dbe (x, y) = E.err E.dummySpan $ printf "Multiple sorts for %s : %s \n" (showpp x) (showpp y)

---------------------------------------------------------------------------
symBinds  :: F.BindEnv -> [SymBinds]
---------------------------------------------------------------------------
symBinds  = M.toList
          . M.map Misc.groupList
          . Misc.group
          . binders

type SymBinds = (F.Symbol, [(F.Sort, [F.BindId])])

binders :: F.BindEnv -> [(F.Symbol, (F.Sort, F.BindId))]
binders be = [(x, (F.sr_sort t, i)) | (i, x, t) <- F.bindEnvToList be]


---------------------------------------------------------------------------
-- | Alpha Rename bindings to ensure each var appears in unique binder
---------------------------------------------------------------------------
renameVV :: F.FInfo a -> F.FInfo a
---------------------------------------------------------------------------
renameVV fi = fi {F.bs = be'}
  where
    vts     = map subcVV $ M.elems $ F.cm fi
    be'     = L.foldl' addVV be vts
    be      = F.bs fi

addVV :: F.BindEnv -> (F.Symbol, F.SortedReft) -> F.BindEnv
addVV b (x, t) = snd $ F.insertBindEnv x t b

subcVV :: F.SubC a -> (F.Symbol, F.SortedReft)
subcVV c = (x, sr)
  where
    sr   = F.slhs c
    x    = F.reftBind $ F.sr_reft sr


---------------------------------------------------------------------------
-- | Drop Higher-Order Binders from Environment
---------------------------------------------------------------------------
dropHigherOrderBinders :: F.FInfo a -> F.FInfo a
---------------------------------------------------------------------------
dropHigherOrderBinders fi = fi { F.bs = bs' , F.cm = cm' , F.ws = ws' }
  where 
    (bs', discards) = dropHOBinders (F.bs fi)
    cm' = M.map (foo discards) (F.cm fi)
    ws' = map (bar discards) (F.ws fi)

foo :: [F.BindId] -> F.SubC a -> F.SubC a
foo discards sc = sc { F.senv = foldr F.deleteIBindEnv (F.senv sc) discards }
bar :: [F.BindId] -> F.WfC a -> F.WfC a
bar discards wf = wf { F.wenv = foldr F.deleteIBindEnv (F.wenv wf) discards }

dropHOBinders :: F.BindEnv -> (F.BindEnv, [F.BindId])
dropHOBinders = filterBindEnv (isFirstOrder . F.sr_sort .  Misc.thd3)

filterBindEnv f be = (F.bindEnvFromList keep, discard')
  where
    (keep, discard) = L.partition f $ F.bindEnvToList be
    discard' = map Misc.fst3 discard

isFirstOrder t        = {- F.traceFix ("isFO: " ++ F.showFix t) -} (foldSort f 0 t <= 1)
  where
    f n (F.FFunc _ _) = n + 1
    f n _             = n
