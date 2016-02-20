-- | Validate and Transform Constraints to Ensure various Invariants -------------------------
--   1. Each binder must be associated with a UNIQUE sort
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Fixpoint.Solver.Validate
       ( -- * Validate FInfo
         validate

         -- * Transform FInfo to enforce invariants
       , sanitize

         -- * Sorts for each Symbol
       , symbolSorts
       )
       where

import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Visitor     (isConcC, isKvarC, mapKVars)
import           Language.Fixpoint.SortCheck        (isFirstOrder)
import qualified Language.Fixpoint.Misc   as Misc
import           Language.Fixpoint.Misc        (fM, errorstar)
import qualified Language.Fixpoint.Types  as F
import qualified Language.Fixpoint.Types.Errors as E
import qualified Data.HashMap.Strict      as M
import qualified Data.HashSet             as S
import qualified Data.List as L
import           Data.Maybe          (isNothing)
import           Control.Monad       ((>=>))
-- import           Text.Printf
import           Text.PrettyPrint.HughesPJ
type ValidateM a = Either E.Error a

---------------------------------------------------------------------------
validate :: F.SInfo a -> ValidateM ()
validate = errorstar "TODO: validate input"
---------------------------------------------------------------------------

---------------------------------------------------------------------------
sanitize :: F.SInfo a -> ValidateM (F.SInfo a)
---------------------------------------------------------------------------
sanitize   = fM dropFuncSortedShadowedBinders
         >=> fM dropWfcFunctions   
         >=>    checkRhsCs
         >=>    banQualifFreeVars
         >=>    banConstraintFreeVars

---------------------------------------------------------------------------
-- | check that no constraint has free variables (ignores kvars)
---------------------------------------------------------------------------
banConstraintFreeVars :: F.SInfo a -> ValidateM (F.SInfo a)
banConstraintFreeVars fi0 = Misc.applyNonNull (Right fi0) (Left . badCs) bads
  where
    fi = mapKVars (const $ Just F.PTrue) fi0
    bads = [c | c <- M.elems $ F.cm fi, not $ cNoFreeVars fi c]

cNoFreeVars :: F.SInfo a -> F.SimpC a -> Bool
cNoFreeVars fi c = S.null $ cRng `nubDiff` (lits ++ cDom ++ F.prims)
  where
    be = F.bs fi
    lits = fst <$> (F.toListSEnv $ F.lits fi)
    ids = F.elemsIBindEnv $ F.senv c
    cDom = [fst $ F.lookupBindEnv i be | i <- ids]
    cRng = concat [S.toList . freeVars . F.sr_reft . snd $ F.lookupBindEnv i be | i <- ids]

--TODO deduplicate (also in Solver/UniqifyBinds)
freeVars :: F.Reft -> S.HashSet F.Symbol
freeVars rft@(F.Reft (v, _)) = S.delete v $ S.fromList $ F.syms rft

badCs :: Misc.ListNE (F.SimpC a) -> E.Error
badCs = E.catErrors . map (E.errFreeVarInConstraint . F.subcId)


---------------------------------------------------------------------------
-- | check that no qualifier has free variables
---------------------------------------------------------------------------
banQualifFreeVars :: F.SInfo a -> ValidateM (F.SInfo a)
---------------------------------------------------------------------------
banQualifFreeVars fi = Misc.applyNonNull (Right fi) (Left . badQuals) bads
  where
    bads   = [ (q, xs) | q <- F.quals fi, let xs = free q, not (null xs) ]
    lits   = fst <$> F.toListSEnv (F.lits fi)
    free q = S.toList $ F.syms (F.q_body q) `nubDiff` (lits ++ F.syms (fst <$> F.q_params q))


badQuals     :: Misc.ListNE (F.Qualifier, Misc.ListNE F.Symbol) -> E.Error
badQuals bqs = E.catErrors [ E.errFreeVarInQual q xs | (q, xs) <- bqs]

-- Null if first is a subset of second
nubDiff :: [F.Symbol] -> [F.Symbol] -> S.HashSet F.Symbol
nubDiff a b = a' `S.difference` b'
  where
    a' = S.fromList a
    b' = S.fromList b

---------------------------------------------------------------------------
-- | check that each constraint has RHS of form [k1,...,kn] or [p]
---------------------------------------------------------------------------
checkRhsCs :: F.SInfo a -> ValidateM (F.SInfo a)
---------------------------------------------------------------------------
checkRhsCs fi = Misc.applyNonNull (Right fi) (Left . badRhs) bads
  where
    ics       = M.toList $ F.cm fi
    bads      = [(i, c) | (i, c) <- ics, not $ isOk c]
    isOk c    = isKvarC c || isConcC c

badRhs :: Misc.ListNE (Integer, F.SimpC a) -> E.Error
badRhs = E.catErrors . map badRhs1

badRhs1 :: (Integer, F.SimpC a) -> E.Error
badRhs1 (i, c) = E.err E.dummySpan $ vcat [ "Malformed RHS for constraint id" <+> pprint i
                                          , nest 4 (pprint (F.crhs c)) ]

-- | Conservative check that KVars appear at "top-level" in pred
-- isOkRhs :: F.Pred -> Bool
-- isOkRhs p = all isKvar ps  || all isConc ps
--  where
--     ps    = F.conjuncts p
---------------------------------------------------------------------------
-- | symbol |-> sort for EVERY variable in the FInfo
---------------------------------------------------------------------------
symbolSorts :: F.GInfo c a -> ValidateM [(F.Symbol, F.Sort)]
---------------------------------------------------------------------------
symbolSorts fi = (normalize . compact . (defs ++)) =<< bindSorts fi
  where
    normalize  = fmap (map (unShadow dm))
    dm         = M.fromList defs
    defs       = F.toListSEnv $ F.lits fi

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
  | otherwise = Left $ dupBindErrors bad'
  where
    bad'      = [(x, (, []) <$> ts) | (x, ts) <- bad]
    (bad, ok) = L.partition multiSorted . binds $ xts
    binds     = M.toList . M.map Misc.sortNub . Misc.group

---------------------------------------------------------------------------
bindSorts  :: F.GInfo c a -> Either E.Error [(F.Symbol, F.Sort)]
---------------------------------------------------------------------------
bindSorts fi
  | null bad   = Right [ (x, t) | (x, [(t, _)]) <- ok ]
  | otherwise  = Left $ dupBindErrors [ (x, ts) | (x, ts) <- bad]
  where
    (bad, ok)  = L.partition multiSorted . binds $ fi
    binds      = symBinds . F.bs


multiSorted :: (x, [t]) -> Bool
multiSorted = (1 <) . length . snd

dupBindErrors :: [(F.Symbol, [(F.Sort, [F.BindId] )])] -> E.Error
dupBindErrors = foldr1 E.catError . map dbe
  where
   dbe (x, y) = E.err E.dummySpan $ vcat [ "Multiple sorts for" <+> pprint x
                                         , nest 4 (pprint y) ]

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


--------------------------------------------------------------------------------
-- | Drop func-sorted `bind` that are shadowed by `constant` (if same type, else error)
--------------------------------------------------------------------------------
dropFuncSortedShadowedBinders :: F.SInfo a -> F.SInfo a
---------------------------------------------------------------------------
dropFuncSortedShadowedBinders fi = dropBinders f (const True) fi
  where
    f x t  = not (M.member x defs) || F.allowHO fi || isFirstOrder t
    defs   = M.fromList $ F.toListSEnv $ F.lits fi

---------------------------------------------------------------------------
-- | Drop functions from WfC environments
--------------------------------------------------------------------------------
dropWfcFunctions :: F.SInfo a -> F.SInfo a
---------------------------------------------------------------------------
dropWfcFunctions fi | F.allowHO fi = fi 
dropWfcFunctions fi = fi { F.ws = ws' }
  where
    nonFunction   = isNothing . F.functionSort
    (_, discards) = filterBindEnv (const nonFunction) $  F.bs fi
    ws'           = deleteWfCBinds discards          <$> F.ws fi


---------------------------------------------------------------------------
-- | Generic API for Deleting Binders from FInfo
---------------------------------------------------------------------------
dropBinders :: KeepBindF -> KeepSortF -> F.SInfo a -> F.SInfo a
---------------------------------------------------------------------------
dropBinders f g fi  = fi { F.bs = bs' , F.cm = cm' , F.ws = ws' , F.lits = lits' }
  where
    discards        = {- tracepp "DISCARDING" -} diss
    (bs', diss)     = filterBindEnv f $ F.bs fi
    cm'             = deleteSubCBinds discards   <$> F.cm fi
    ws'             = deleteWfCBinds  discards   <$> F.ws fi
    lits'           = F.filterSEnv g (F.lits fi)

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
