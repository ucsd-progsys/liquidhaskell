-- | Validate and Transform Constraints to Ensure various Invariants -------------------------
--   1. Each binder must be associated with a UNIQUE sort
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Fixpoint.Solver.Validate
       ( -- * Transform FInfo to enforce invariants
         sanitize

         -- * Sorts for each Symbol
       , symbolSorts
       )
       where

import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Visitor (isConcC, isKvarC, mapKVars, mapKVarSubsts)
import           Language.Fixpoint.SortCheck     (isFirstOrder)
import qualified Language.Fixpoint.Misc                            as Misc
import qualified Language.Fixpoint.Types                           as F
import           Language.Fixpoint.Types.Config (Config, allowHO)
import qualified Language.Fixpoint.Types.Errors                    as E
import           Language.Fixpoint.Graph (kvEdges, CVertex (..))
import qualified Data.HashMap.Strict                               as M
import qualified Data.HashSet                                      as S
import qualified Data.List                                         as L
import qualified Data.Text                                         as T
import           Data.Maybe          (isNothing, mapMaybe)
import           Control.Monad       ((>=>))
import           Text.PrettyPrint.HughesPJ

type ValidateM a = Either E.Error a

--------------------------------------------------------------------------------
sanitize :: F.SInfo a -> ValidateM (F.SInfo a)
--------------------------------------------------------------------------------
sanitize   =    -- banIllScopedKvars
             Misc.fM dropFuncSortedShadowedBinders
         >=> Misc.fM sanitizeWfC
         >=> Misc.fM replaceDeadKvars
         >=> Misc.fM dropBogusSubstitutions
         >=>         banMixedRhs
         >=>         banQualifFreeVars
         >=>         banConstraintFreeVars


--------------------------------------------------------------------------------
-- | See issue liquid-fixpoint issue #230. This checks that whenever we have,
--      G1        |- K.su1
--      G2, K.su2 |- rhs
--   then
--      G1 \cap G2 \subseteq wenv(k)
--------------------------------------------------------------------------------
_banIllScopedKvars :: F.SInfo a ->  ValidateM (F.SInfo a)
--------------------------------------------------------------------------------
_banIllScopedKvars si = Misc.applyNonNull (Right si) (Left . badKs) errs
  where
    errs             = concatMap (checkIllScope si kDs) ks
    kDs              = kvarDefUses si
    ks               = filter notKut $ M.keys (F.ws si)
    notKut           = not . (`F.ksMember` F.kuts si)

badKs :: [(F.KVar, F.SubcId, F.SubcId, F.IBindEnv)] -> F.Error
badKs = E.catErrors . map E.errIllScopedKVar

type KvConstrM = M.HashMap F.KVar [Integer]
type KvDefs    = (KvConstrM, KvConstrM)

checkIllScope :: F.SInfo a -> KvDefs -> F.KVar -> [(F.KVar, F.SubcId, F.SubcId, F.IBindEnv)]
checkIllScope si (inM, outM) k = mapMaybe (uncurry (isIllScope si k)) ios
  where
    ios                        = [(i, o) | i <- ins, o <- outs, i /= o ]
    ins                        = M.lookupDefault [] k inM
    outs                       = M.lookupDefault [] k outM

isIllScope :: F.SInfo a -> F.KVar -> F.SubcId -> F.SubcId -> Maybe (F.KVar, F.SubcId, F.SubcId, F.IBindEnv)
isIllScope si k inI outI
  | F.nullIBindEnv badXs = Nothing
  | otherwise            = Just (k, inI, outI, badXs)
  where
    badXs                = F.diffIBindEnv commonXs kXs
    kXs                  = {- F.tracepp ("kvarBinds " ++ show k) $ -} kvarBinds si k
    commonXs             = F.intersectionIBindEnv inXs outXs
    inXs                 = subcBinds si inI
    outXs                = subcBinds si outI

subcBinds :: F.SInfo a -> F.SubcId -> F.IBindEnv
subcBinds si i = F._cenv $ F.cm si M.! i

kvarBinds :: F.SInfo a -> F.KVar -> F.IBindEnv
kvarBinds si = F.wenv . (F.ws si M.!)

kvarDefUses :: F.SInfo a -> KvDefs
kvarDefUses si = (Misc.group ins, Misc.group outs)
  where
    es         = kvEdges si
    outs       = [(k, o) | (KVar k, Cstr o) <- es ]
    ins        = [(k, i) | (Cstr i, KVar k) <- es ]



--------------------------------------------------------------------------------
-- | remove substitutions `K[x := e]` where `x` is not in the domain of K or `e`
--   is not a "known" var, i.e. one corresponding to some binder.
--------------------------------------------------------------------------------
dropBogusSubstitutions :: F.SInfo a -> F.SInfo a
dropBogusSubstitutions si0 = mapKVarSubsts (F.filterSubst . keepSubst) si0
  where
    kvM                    = kvarDomainM si0
    kvXs k                 = M.lookupDefault S.empty k kvM
    keepSubst k x e        = x `S.member` kvXs k && knownRhs e
    knownRhs (F.EVar y)    = y `S.member` xs
    knownRhs _             = False
    xs                     = knownVars si0

knownVars :: F.SInfo a -> S.HashSet F.Symbol
knownVars si = S.fromList vs
  where
    vs       = [ y | (_, x, F.RR _ (F.Reft (v,_))) <- F.bindEnvToList . F.bs $ si
                   , y <- [x, v] ]

type KvDom     = M.HashMap F.KVar (S.HashSet F.Symbol)

kvarDomainM :: F.SInfo a -> KvDom
kvarDomainM si = M.fromList [ (k, dom k) | k <- ks ]
  where
    ks         = M.keys (F.ws si)
    dom        = S.fromList . F.kvarDomain si





--------------------------------------------------------------------------------
-- | check that no constraint has free variables (ignores kvars)
--------------------------------------------------------------------------------
banConstraintFreeVars :: F.SInfo a -> ValidateM (F.SInfo a)
banConstraintFreeVars fi0 = Misc.applyNonNull (Right fi0) (Left . badCs) bads
  where
    fi = mapKVars (const $ Just F.PTrue) fi0
    bads = [(c, fs) | c <- M.elems $ F.cm fi, Just fs <- [cNoFreeVars fi c]]

cNoFreeVars :: F.SInfo a -> F.SimpC a -> Maybe [F.Symbol]
cNoFreeVars fi c = if S.null fv then Nothing else Just (S.toList fv)
  where
    be   = F.bs fi
    lits = fst <$> F.toListSEnv (F.gLits fi)
    ids  = F.elemsIBindEnv $ F.senv c
    cDom = [fst $ F.lookupBindEnv i be | i <- ids]
    cRng = concat [S.toList . F.reftFreeVars . F.sr_reft . snd $ F.lookupBindEnv i be | i <- ids]
    fv   = cRng `nubDiff` (lits ++ cDom ++ F.prims)

badCs :: Misc.ListNE (F.SimpC a, [F.Symbol]) -> E.Error
badCs = E.catErrors . map (E.errFreeVarInConstraint . (Misc.mapFst F.subcId))


--------------------------------------------------------------------------------
-- | check that no qualifier has free variables
--------------------------------------------------------------------------------
banQualifFreeVars :: F.SInfo a -> ValidateM (F.SInfo a)
--------------------------------------------------------------------------------
banQualifFreeVars fi = Misc.applyNonNull (Right fi) (Left . badQuals) bads
  where
    bads   = [ (q, xs) | q <- F.quals fi, let xs = free q, not (null xs) ]
    lits   = fst <$> F.toListSEnv (F.gLits fi)
    free q = S.toList $ F.syms (F.qBody q) `nubDiff` (lits ++ F.prims ++ F.syms (fst <$> F.qParams q))


badQuals     :: Misc.ListNE (F.Qualifier, Misc.ListNE F.Symbol) -> E.Error
badQuals bqs = E.catErrors [ E.errFreeVarInQual q xs | (q, xs) <- bqs]

-- Null if first is a subset of second
nubDiff :: [F.Symbol] -> [F.Symbol] -> S.HashSet F.Symbol
nubDiff a b = a' `S.difference` b'
  where
    a' = S.fromList a
    b' = S.fromList b

--------------------------------------------------------------------------------
-- | check that each constraint has RHS of form [k1,...,kn] or [p]
--------------------------------------------------------------------------------
banMixedRhs :: F.SInfo a -> ValidateM (F.SInfo a)
--------------------------------------------------------------------------------
banMixedRhs fi = Misc.applyNonNull (Right fi) (Left . badRhs) bads
  where
    ics        = M.toList $ F.cm fi
    bads       = [(i, c) | (i, c) <- ics, not $ isOk c]
    isOk c     = isKvarC c || isConcC c

badRhs :: Misc.ListNE (Integer, F.SimpC a) -> E.Error
badRhs = E.catErrors . map badRhs1

badRhs1 :: (Integer, F.SimpC a) -> E.Error
badRhs1 (i, c) = E.err E.dummySpan $ vcat [ "Malformed RHS for constraint id" <+> pprint i
                                          , nest 4 (pprint (F.crhs c)) ]

--------------------------------------------------------------------------------
-- | symbol |-> sort for EVERY variable in the FInfo
--------------------------------------------------------------------------------
symbolSorts :: Config -> F.GInfo c a -> [(F.Symbol, F.Sort)]
symbolSorts cfg fi = either E.die id $ symbolSorts' cfg fi

symbolSorts' :: Config -> F.GInfo c a -> ValidateM [(F.Symbol, F.Sort)]
symbolSorts' cfg fi  = (normalize . compact . (defs ++)) =<< bindSorts fi
  where
    normalize       = fmap (map (unShadow txFun dm))
    dm              = M.fromList defs
    defs            = F.toListSEnv $ F.gLits fi
    txFun
      | allowHO cfg = id
      | otherwise   = defuncSort

unShadow :: (F.Sort -> F.Sort) -> M.HashMap F.Symbol a -> (F.Symbol, F.Sort) -> (F.Symbol, F.Sort)
unShadow tx dm (x, t)
  | M.member x dm  = (x, t)
  | otherwise      = (x, tx t)

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

--------------------------------------------------------------------------------
bindSorts  :: F.GInfo c a -> Either E.Error [(F.Symbol, F.Sort)]
--------------------------------------------------------------------------------
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

--------------------------------------------------------------------------------
symBinds  :: F.BindEnv -> [SymBinds]
--------------------------------------------------------------------------------
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
--------------------------------------------------------------------------------
dropFuncSortedShadowedBinders fi = dropBinders f (const True) fi
  where
    f x t  = not (M.member x defs) || F.allowHO fi || isFirstOrder t
    defs   = M.fromList $ F.toListSEnv $ F.gLits fi

--------------------------------------------------------------------------------
-- | Drop irrelevant binders from WfC Environments
--------------------------------------------------------------------------------
sanitizeWfC :: F.SInfo a -> F.SInfo a
sanitizeWfC si = si { F.ws = ws' }
  where
    ws'        = deleteWfCBinds drops <$> F.ws si
    (_,drops)  = filterBindEnv keepF   $  F.bs si
    keepF      = conjKF [nonConstantF si, nonFunctionF si, _nonDerivedLH]
    -- drops   = F.tracepp "sanitizeWfC: dropping" $ L.sort drops'

conjKF :: [KeepBindF] -> KeepBindF
conjKF fs x t = and [f x t | f <- fs]

-- | `nonDerivedLH` keeps a bind x if it does not start with `$` which is used
--   typically for names that are automatically "derived" by GHC (and which can)
--   blow up the environments thereby clogging instantiation, etc.
--   NOTE: This is an LH specific hack and should be moved there.

_nonDerivedLH :: KeepBindF
_nonDerivedLH x _ = not . T.isPrefixOf "$" . last . T.split ('.' ==) . F.symbolText $ x

nonConstantF :: F.SInfo a -> KeepBindF
nonConstantF si = \x _ -> not (x `F.memberSEnv` cEnv)
  where
    cEnv        = F.gLits si

nonFunctionF :: F.SInfo a -> KeepBindF
nonFunctionF si
  | F.allowHO si    = \_ _ -> True
  | otherwise       = \_ t -> isNothing (F.functionSort t)

--------------------------------------------------------------------------------
-- | Generic API for Deleting Binders from FInfo
--------------------------------------------------------------------------------
dropBinders :: KeepBindF -> KeepSortF -> F.SInfo a -> F.SInfo a
--------------------------------------------------------------------------------
dropBinders f g fi  = fi { F.bs    = bs'
                         , F.cm    = cm'
                         , F.ws    = ws'
                         , F.gLits = lits' }
  where
    discards        = diss
    (bs', diss)     = filterBindEnv f $ F.bs fi
    cm'             = deleteSubCBinds discards   <$> F.cm fi
    ws'             = deleteWfCBinds  discards   <$> F.ws fi
    lits'           = F.filterSEnv g (F.gLits fi)

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


---------------------------------------------------------------------------
-- | Replace KVars that do not have a WfC with PFalse
---------------------------------------------------------------------------
replaceDeadKvars :: F.SInfo a -> F.SInfo a
---------------------------------------------------------------------------
replaceDeadKvars fi = mapKVars go fi
  where
    go k | k `M.member` F.ws fi = Nothing
         | otherwise            = Just F.PFalse
