-- | Validate and Transform Constraints to Ensure various Invariants -------------------------
--   1. Each binder must be associated with a UNIQUE sort

module Language.Fixpoint.Solver.Validate
       ( -- * Validate and Transform FInfo to enforce invariants
         validate

         -- * Sorts for each Symbol
       , symbolSorts

       , finfoDefs
       )
       where

import           Language.Fixpoint.Config
import           Language.Fixpoint.PrettyPrint
import           Language.Fixpoint.Visitor (kvars)
import           Language.Fixpoint.Sort (isFirstOrder)
import qualified Language.Fixpoint.Misc   as Misc
import qualified Language.Fixpoint.Types  as F
import qualified Language.Fixpoint.Errors as E
import qualified Data.HashMap.Strict      as M
import qualified Data.List as L
import           Control.Applicative ((<$>))
import           Text.Printf

type ValidateM a = Either E.Error a

---------------------------------------------------------------------------
validate :: Config -> F.SInfo a -> ValidateM (F.SInfo a)
---------------------------------------------------------------------------
validate _ = Right
           . dropFuncSortedShadowedBinders
           . dropHigherOrderBinders
           . removeExtraWfCs
           -- . renameVV

---------------------------------------------------------------------------
-- | symbol |-> sort for EVERY variable in the FInfo
---------------------------------------------------------------------------
symbolSorts :: F.GInfo c a -> ValidateM [(F.Symbol, F.Sort)]
---------------------------------------------------------------------------
symbolSorts fi = (normalize . compact . (defs ++)) =<< bindSorts fi
  where
    normalize  = fmap (map (unShadow dm))
    dm         = M.fromList defs
    defs       = finfoDefs fi

finfoDefs :: F.GInfo c a -> [(F.Symbol, F.Sort)]
finfoDefs fi = {- THIS KILLS ELIM: tracepp "defs" $ -} lits ++ consts
  where
    lits     = F.lits fi
    consts   = [(x, t) | (x, F.RR t _) <- F.toListSEnv $ F.gs fi]

unShadow :: M.HashMap F.Symbol a -> (F.Symbol, F.Sort) -> (F.Symbol, F.Sort)
unShadow dm (x, t)
  | M.member x dm  = (x, t)
  | otherwise      = (x, defuncSort t)

defuncSort :: F.Sort -> F.Sort
defuncSort (F.FFunc {}) = F.funcSort
defuncSort t            = t

compact :: [(F.Symbol, F.Sort)] -> Either E.Error [(F.Symbol, F.Sort)]
compact xts
  | null bad  = Right [(x, t) | (x, [t]) <- ok ]
  | otherwise = Left $ dupBindErrors bad
  where
    (bad, ok) = L.partition multiSorted . binds $ xts
    binds     = M.toList . M.map Misc.sortNub . Misc.group

---------------------------------------------------------------------------
bindSorts  :: F.GInfo c a -> Either E.Error [(F.Symbol, F.Sort)]
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
symBinds  = {- THIS KILLS ELEM: tracepp "symBinds" . -}
            M.toList
          . M.map Misc.groupList
          . Misc.group
          . binders

type SymBinds = (F.Symbol, [(F.Sort, [F.BindId])])

binders :: F.BindEnv -> [(F.Symbol, (F.Sort, F.BindId))]
binders be = [(x, (F.sr_sort t, i)) | (i, x, t) <- F.bindEnvToList be]


---------------------------------------------------------------------------
-- | Drop WfCs that do not have a KVar (TODO - check well-sorted first?)
---------------------------------------------------------------------------
removeExtraWfCs :: F.SInfo a -> F.SInfo a
---------------------------------------------------------------------------
removeExtraWfCs fi = fi { F.ws = filter hasKVar $ F.ws fi }
  where
    hasKVar = not . null . kvars . F.wrft


---------------------------------------------------------------------------
-- | Drop func-sorted `bind` that are shadowed by `constant` (if same type, else error)
---------------------------------------------------------------------------
dropFuncSortedShadowedBinders :: F.SInfo a -> F.SInfo a
---------------------------------------------------------------------------
dropFuncSortedShadowedBinders fi = dropBinders f (const True) fi
  where
    f x t              = (not $ M.member x defs) || isFirstOrder t
    defs               = M.fromList $ finfoDefs fi

---------------------------------------------------------------------------
-- | Drop Higher-Order Binders and Constants from Environment
---------------------------------------------------------------------------
dropHigherOrderBinders :: F.SInfo a -> F.SInfo a
---------------------------------------------------------------------------
dropHigherOrderBinders = dropBinders (const isFirstOrder) isFirstOrder

---------------------------------------------------------------------------
-- | Generic API for Deleting Binders from FInfo
---------------------------------------------------------------------------
dropBinders :: KeepBindF -> KeepSortF -> F.SInfo a -> F.SInfo a
---------------------------------------------------------------------------
dropBinders f g fi  = fi { F.bs = bs' , F.cm = cm' , F.ws = ws' , F.gs = gs' }
  where
    discards        = tracepp "DISCARDING" diss
    (bs', diss)     = filterBindEnv f $ F.bs fi
    cm'             = deleteSubCBinds discards   <$> F.cm fi
    ws'             = deleteWfCBinds  discards   <$> F.ws fi
    gs'             = F.filterSEnv (g . F.sr_sort) (F.gs fi)

type KeepBindF = F.Symbol -> F.Sort -> Bool
type KeepSortF = F.Sort -> Bool

deleteSubCBinds :: [F.BindId] -> F.SimpC a -> F.SimpC a
deleteSubCBinds bs sc = sc { F._cenv = foldr F.deleteIBindEnv (F.senv sc) bs }

deleteWfCBinds :: [F.BindId] -> F.WfC a -> F.WfC a
deleteWfCBinds bs wf = wf { F.wenv = foldr F.deleteIBindEnv (F.wenv wf) bs }

filterBindEnv :: KeepBindF -> F.BindEnv -> (F.BindEnv, [F.BindId])
filterBindEnv f be  = (F.bindEnvFromList keep, discard')
  where
    (keep, discard) = L.partition f' $ F.bindEnvToList be
    discard'        = Misc.fst3     <$> discard
    f' (_, x, t)    = f x (F.sr_sort t)
