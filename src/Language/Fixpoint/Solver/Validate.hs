-- | Validate and Transform Constraints to Ensure various Invariants -------------------------
--   1. Each binder must be associated with a UNIQUE sort

module Language.Fixpoint.Solver.Validate
       ( -- * Validate and Transform FInfo to enforce invariants
         validate

         -- * Rename VV binders in each constraint to be unique
       , renameVV

         -- * Sorts for each Symbol
       , symbolSorts

       , finfoDefs
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
import           Control.Applicative ((<$>))
import           Text.Printf

type ValidateM a = Either E.Error a

---------------------------------------------------------------------------
validate :: Config -> F.FInfo a -> ValidateM (F.FInfo a)
---------------------------------------------------------------------------
validate _ = Right
           -- . dropShadowedBinders
           . dropHigherOrderBinders
           -- . renameVV

---------------------------------------------------------------------------
-- | symbol |-> sort for EVERY variable in the FInfo
---------------------------------------------------------------------------
symbolSorts :: F.FInfo a -> ValidateM [(F.Symbol, F.Sort)]
---------------------------------------------------------------------------
symbolSorts fi = (normalize . compact . (defs ++)) =<< bindSorts fi
  where
    normalize  = fmap (map (unShadow dm))
    dm         = M.fromList defs
    defs       = finfoDefs fi

finfoDefs :: F.FInfo a -> [(F.Symbol, F.Sort)]
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
symBinds  = {- THIS KILLS ELEM: tracepp "symBinds" . -}
            M.toList
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
-- | Drop func-sorted `bind` that are shadowed by `constant` (if same type, else error)
---------------------------------------------------------------------------
dropShadowedBinders :: F.FInfo a -> F.FInfo a
---------------------------------------------------------------------------
dropShadowedBinders fi = dropBinders f (const True) fi
  where
    f x t              = (not $ M.member x defs) || isFirstOrder t
    defs               = M.fromList $ finfoDefs fi

{-
CUT ME
  CUT ME fi = fi { F.cm = cm', F.bs = bs' }
  CUT ME where
    CUT ME cm'          = unshadowSubC    sh <$> F.cm fi
    CUT ME bs'          = unshadowBindEnv sh     bs
    CUT ME sh           = findShadowedBinds defs bs
    CUT ME bs           = F.bs fi
    CUT ME defs         = M.fromList $ finfoDefs fi
CUT ME
CUT ME type SyEnv       = M.Map F.Symbol F.Sort
CUT ME type ShadowBinds = M.Map F.BindId ()
CUT ME
CUT ME findShadowedBinds :: SyEnv -> F.BindEnv -> ShadowBinds
CUT ME findShadowedBinds = error "TODO"
CUT ME
CUT ME unshadowBindEnv :: ShadowBinds -> F.BindEnv -> F.BindEnv
CUT ME unshadowBindEnv = error "TODO"
CUT ME
CUT ME unshadowSubC :: ShadowBinds -> F.SubC a -> F.SubC a
CUT ME unshadowSubC sh c = c { error "TODO"
CUT ME
CUT ME unshadowIBindEnv :: ShadowBinds -> F.IBindEnv -> F.IBindEnv
CUT ME unshadowIBindEnv = error "TODO"
CUT ME
CUT ME -- 1. build constants (easy)
CUT ME -- 2. find dodgy binds
CUT ME -- 3. remove dodgy binds
CUT ME
CUT ME
CUT ME -- dropHigherOrderBinders fi = fi { F.bs = bs' , F.cm = cm' , F.ws = ws' , F.gs = gs' }
  CUT ME -- where
    CUT ME -- (bs', discards) = dropHOBinders (F.bs fi)
    CUT ME -- cm' = deleteSubCBinds discards <$> F.cm fi
    CUT ME -- ws' = deleteWfCBinds  discards <$> F.ws fi
    CUT ME -- gs' = F.filterSEnv (isFirstOrder . F.sr_sort) (F.gs fi)
CUT ME
-}
---------------------------------------------------------------------------
-- | Drop Higher-Order Binders and Constants from Environment
---------------------------------------------------------------------------
dropHigherOrderBinders :: F.FInfo a -> F.FInfo a
---------------------------------------------------------------------------
dropHigherOrderBinders = dropBinders (const isFirstOrder) isFirstOrder

isFirstOrder :: F.Sort -> Bool
isFirstOrder t        = foldSort f 0 t <= 1
  where
    f n (F.FFunc _ _) = n + 1
    f n _             = n

---------------------------------------------------------------------------
-- | Generic API for Deleting Binders from FInfo
---------------------------------------------------------------------------
dropBinders :: KeepBindF -> KeepSortF -> F.FInfo a -> F.FInfo a
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

deleteSubCBinds :: [F.BindId] -> F.SubC a -> F.SubC a
deleteSubCBinds bs sc = sc { F.senv = foldr F.deleteIBindEnv (F.senv sc) bs }

deleteWfCBinds :: [F.BindId] -> F.WfC a -> F.WfC a
deleteWfCBinds bs wf = wf { F.wenv = foldr F.deleteIBindEnv (F.wenv wf) bs }

filterBindEnv :: KeepBindF -> F.BindEnv -> (F.BindEnv, [F.BindId])
filterBindEnv f be  = (F.bindEnvFromList keep, discard')
  where
    (keep, discard) = L.partition f' $ F.bindEnvToList be
    discard'        = Misc.fst3     <$> discard
    f' (_, x, t)    = f x (F.sr_sort t)
