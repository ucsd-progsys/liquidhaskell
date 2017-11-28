{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Haskell.Liquid.Types.PredType (
    PrType
  , TyConP (..), DataConP (..)
  , dataConTy
  , dataConPSpecType
  , makeTyConInfo
  , replacePreds

  , replacePredsWithRefs
  , pVartoRConc

  -- * Dummy `Type` that represents _all_ abstract-predicates
  , predType

  -- * Compute @RType@ of a given @PVar@
  , pvarRType

  , substParg
  , pApp
  , pappSort
  , pappArity

  -- * should be elsewhere
  , dataConWorkRep
  ) where

import           Prelude                         hiding (error)
import           DataCon
import           Name                            (getSrcSpan)
import           Text.PrettyPrint.HughesPJ
import qualified TyCon                           as TC
-- import qualified Var
import           Type
import           Var
import           Language.Haskell.Liquid.GHC.TypeRep
import           Data.Hashable
import qualified Data.HashMap.Strict             as M
import           Data.List                       (foldl', partition)

import           Language.Fixpoint.Misc

-- import           Language.Fixpoint.Types         hiding (Expr, Predicate)
import qualified Language.Fixpoint.Types         as F
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types.RefType hiding (generalize)
import           Language.Haskell.Liquid.Types
import           Data.List                       (nub)
import           Data.Default

makeTyConInfo :: [(TC.TyCon, TyConP)] -> M.HashMap TC.TyCon RTyCon
makeTyConInfo = hashMapMapWithKey mkRTyCon . M.fromList

mkRTyCon ::  TC.TyCon -> TyConP -> RTyCon
mkRTyCon tc (TyConP _ αs' ps _ tyvariance predvariance size)
  = RTyCon tc pvs' (mkTyConInfo tc tyvariance predvariance size)
  where
    τs   = [rVar α :: RSort |  α <- tyConTyVarsDef tc]
    pvs' = subts (zip αs' τs) <$> ps

-- TODO: duplicated with Liquid.Measure.makeDataConType
dataConPSpecType :: DataCon -> DataConP -> [(Var, SpecType)]
dataConPSpecType dc dcp = [ (workX, workT), (wrapX, wrapT) ]
  where
    workT | isVanilla   = wrapT
          | otherwise   = dcWorkSpecType dc wrapT
    wrapT               = dcWrapSpecType dc dcp
    workX               = dataConWorkId dc            -- this is the weird one for GADTs
    wrapX               = dataConWrapId dc            -- this is what the user expects to see
    isVanilla           = F.notracepp ("IS-Vanilla: " ++ showpp dc) $ isVanillaDataCon dc

dcWorkSpecType :: DataCon -> SpecType -> SpecType
dcWorkSpecType c wrT    = fromRTypeRep (meetWorkWrapRep c wkR wrR)
  where
    wkR                 = dataConWorkRep c
    wrR                 = toRTypeRep wrT

dataConWorkRep :: DataCon -> SpecRep
dataConWorkRep c = toRTypeRep
                 -- . F.tracepp ("DCWR-2: " ++ F.showpp c)
                 . ofType
                 -- . F.tracepp ("DCWR-1: " ++ F.showpp c)
                 . dataConRepType
                 -- . Var.varType
                 -- . dataConWorkId
                 $ c
{-
dataConWorkRep :: DataCon -> SpecRep
dataConWorkRep dc = RTypeRep
  { ty_vars   = as
  , ty_preds  = []
  , ty_labels = []
  , ty_binds  = replicate nArgs F.dummySymbol
  , ty_refts  = replicate nArgs mempty
  , ty_args   = ts'
  , ty_res    = t'
  }
  where
    (ts', t')          = F.tracepp "DCWR-1" (ofType <$> ts, ofType t)
    as                 = makeRTVar . rTyVar <$> αs
    tArg
    (αs,_,eqs,th,ts,t) = dataConFullSig dc
    nArgs              = length ts

dataConResultTy :: DataCon -> [TyVar] -> Type -> Type
dataConResultTy dc αs t = mkFamilyTyConApp tc tArgs'
  where
    tArgs'              = take (nArgs - nVars) tArgs ++ (mkTyVarTy <$> αs)
    nVars               = length αs
    nArgs               = length tArgs
    (tc, tArgs)         = fromMaybe err (splitTyConApp_maybe _t)
    err                 = GM.namedPanic dc ("Cannot split result type of DataCon " ++ show dc)

  --  t                 = RT.ofType  $  mkFamilyTyConApp tc tArgs'
  -- as                = makeRTVar . rTyVar <$> αs
  --  (αs,_,_,_,_ts,_t) = dataConFullSig dc

-}

meetWorkWrapRep :: DataCon -> SpecRep -> SpecRep -> SpecRep
meetWorkWrapRep c workR wrapR
  | 0 <= pad
  = workR { ty_binds = xs ++ (ty_binds wrapR)
          , ty_args  = ts ++ zipWith strengthenRType ts' (ty_args wrapR)
          , ty_res   = strengthenRType (ty_res workR)    (ty_res  wrapR)
          }
  | otherwise
  = panic (Just (getSrcSpan c)) errMsg
  where
    pad       = {- F.tracepp ("MEETWKRAP: " ++ show (ty_vars workR)) $ -} workN - wrapN
    (xs, _)   = splitAt pad (ty_binds workR)
    (ts, ts') = splitAt pad (ty_args  workR)
    workN     = length      (ty_args  workR)
    wrapN     = length      (ty_args  wrapR)
    errMsg    = "Unsupported Work/Wrap types for Data Constructor " ++ showPpr c

strengthenRType :: SpecType -> SpecType -> SpecType
strengthenRType wkT wrT = maybe wkT (strengthen wkT) (stripRTypeBase wrT)

dcWrapSpecType :: DataCon -> DataConP -> SpecType
dcWrapSpecType dc (DataConP _ vs ps ls cs yts rt _ _ _)
  = {- F.tracepp ("dcWrapSpecType: " ++ show dc ++ " " ++ F.showpp rt) $ -}
    mkArrow makeVars ps ls ts' rt'
  where
    (xs, ts) = unzip (reverse yts)
    mkDSym z = (F.symbol z) `F.suffixSymbol` (F.symbol dc)
    ys       = mkDSym <$> xs
    tx _  []     []     []     = []
    tx su (x:xs) (y:ys) (t:ts) = (y, F.subst (F.mkSubst su) t, mempty)
                               : tx ((x, F.EVar y):su) xs ys ts
    tx _ _ _ _ = panic Nothing "PredType.dataConPSpecType.tx called on invalid inputs"
    yts'     = tx [] xs ys ts
    ts'      = map ("" , , mempty) cs ++ yts'
    su       = F.mkSubst [(x, F.EVar y) | (x, y) <- zip xs ys]
    rt'      = F.subst su rt
    makeVars = zipWith (\v a -> RTVar v (rTVarInfo a :: RTVInfo RSort)) vs (fst $ splitForAllTys $ dataConRepType dc)

instance PPrint TyConP where
  pprintTidy k (TyConP _ vs ps ls _ _ _)
    = (parens $ hsep (punctuate comma (pprintTidy k <$> vs))) <+>
      (parens $ hsep (punctuate comma (pprintTidy k <$> ps))) <+>
      (parens $ hsep (punctuate comma (pprintTidy k <$> ls)))

instance Show TyConP where
 show = showpp -- showSDoc . ppr

instance PPrint DataConP where
  pprintTidy k (DataConP _ vs ps ls cs yts t isGadt mname _)
     =  (parens $ hsep (punctuate comma (pprintTidy k <$> vs)))
    <+> (parens $ hsep (punctuate comma (pprintTidy k <$> ps)))
    <+> (parens $ hsep (punctuate comma (pprintTidy k <$> ls)))
    <+> (parens $ hsep (punctuate comma (pprintTidy k <$> cs)))
    <+> (parens $ hsep (punctuate comma (pprintTidy k <$> yts)))
    <+> (pprintTidy k isGadt)
    <+> (pprintTidy k mname)
    <+>  pprintTidy k t

instance Show DataConP where
  show = showpp

dataConTy :: Monoid r
          => M.HashMap RTyVar (RType RTyCon RTyVar r)
          -> Type -> RType RTyCon RTyVar r
dataConTy m (TyVarTy v)
  = M.lookupDefault (rVar v) (RTV v) m
dataConTy m (FunTy t1 t2)
  = rFun F.dummySymbol (dataConTy m t1) (dataConTy m t2)
dataConTy m (ForAllTy (TvBndr α _) t) -- α :: TyVar
  = RAllT (makeRTVar (RTV α)) (dataConTy m t)
dataConTy m (TyConApp c ts)
  = rApp c (dataConTy m <$> ts) [] mempty
dataConTy _ _
  = panic Nothing "ofTypePAppTy"

----------------------------------------------------------------------------
----- Interface: Replace Predicate With Uninterprented Function Symbol -----
----------------------------------------------------------------------------

replacePredsWithRefs :: (UsedPVar, (F.Symbol, [((), F.Symbol, F.Expr)]) -> F.Expr)
                     -> UReft F.Reft -> UReft F.Reft
replacePredsWithRefs (p, r) (MkUReft (F.Reft(v, rs)) (Pr ps) s)
  = MkUReft (F.Reft (v, rs'')) (Pr ps2) s
  where
    rs''             = mconcat $ rs : rs'
    rs'              = r . (v,) . pargs <$> ps1
    (ps1, ps2)       = partition (== p) ps

pVartoRConc :: PVar t -> (F.Symbol, [(a, b, F.Expr)]) -> F.Expr
pVartoRConc p (v, args) | length args == length (pargs p)
  = pApp (pname p) $ F.EVar v : (thd3 <$> args)

pVartoRConc p (v, args)
  = pApp (pname p) $ F.EVar v : args'
  where
    args' = (thd3 <$> args) ++ (drop (length args) (thd3 <$> pargs p))

-----------------------------------------------------------------------
-- | @pvarRType π@ returns a trivial @RType@ corresponding to the
--   function signature for a @PVar@ @π@. For example, if
--      @π :: T1 -> T2 -> T3 -> Prop@
--   then @pvarRType π@ returns an @RType@ with an @RTycon@ called
--   @predRTyCon@ `RApp predRTyCon [T1, T2, T3]`
-----------------------------------------------------------------------
pvarRType :: (PPrint r, F.Reftable r) => PVar RSort -> RRType r
-----------------------------------------------------------------------
pvarRType (PV _ k {- (PVProp τ) -} _ args) = rpredType k (fst3 <$> args) -- (ty:tys)
  -- where
  --   ty  = uRTypeGen τ
  --   tys = uRTypeGen . fst3 <$> args


-- rpredType    :: (PPrint r, Reftable r) => PVKind (RRType r) -> [RRType r] -> RRType r
rpredType :: F.Reftable r
          => PVKind (RType RTyCon tv a)
          -> [RType RTyCon tv a] -> RType RTyCon tv r
rpredType (PVProp t) ts = RApp predRTyCon  (uRTypeGen <$> t : ts) [] mempty
rpredType PVHProp    ts = RApp wpredRTyCon (uRTypeGen <$>     ts) [] mempty

predRTyCon   :: RTyCon
predRTyCon   = symbolRTyCon predName

wpredRTyCon   :: RTyCon
wpredRTyCon   = symbolRTyCon wpredName

symbolRTyCon   :: F.Symbol -> RTyCon
symbolRTyCon n = RTyCon (stringTyCon 'x' 42 $ F.symbolString n) [] def

-------------------------------------------------------------------------------------
-- | Instantiate `PVar` with `RTProp` -----------------------------------------------
-------------------------------------------------------------------------------------
-- | @replacePreds@ is the main function used to substitute an (abstract)
--   predicate with a concrete Ref, that is either an `RProp` or `RHProp`
--   type. The substitution is invoked to obtain the `SpecType` resulting
--   at /predicate application/ sites in 'Language.Haskell.Liquid.Constraint'.
--   The range of the `PVar` substitutions are /fresh/ or /true/ `RefType`.
--   That is, there are no further _quantified_ `PVar` in the target.
-------------------------------------------------------------------------------------
replacePreds                 :: String -> SpecType -> [(RPVar, SpecProp)] -> SpecType
-------------------------------------------------------------------------------------
replacePreds msg                 = foldl' go
  where
     go _ (_, RProp _ (RHole _)) = panic Nothing "replacePreds on RProp _ (RHole _)"
     go z (π, t) = substPred msg   (π, t)     z


-- TODO: replace `replacePreds` with
-- instance SubsTy RPVar (Ref RReft SpecType) SpecType where
--   subt (pv, r) t = replacePreds "replacePred" t (pv, r)

-- replacePreds :: String -> SpecType -> [(RPVar, Ref Reft RefType)] -> SpecType
-- replacePreds msg       = foldl' go
--   where go z (π, RProp t) = substPred msg   (π, t)     z
--         go z (π, RPropP r) = replacePVarReft (π, r) <$> z

-------------------------------------------------------------------------------
substPred :: String -> (RPVar, SpecProp) -> SpecType -> SpecType
-------------------------------------------------------------------------------

substPred _   (π, RProp ss (RVar a1 r1)) t@(RVar a2 r2)
  | isPredInReft && a1 == a2    = RVar a1 $ meetListWithPSubs πs ss r1 r2'
  | isPredInReft                = panic Nothing ("substPred RVar Var Mismatch" ++ show (a1, a2))
  | otherwise                   = t
  where
    (r2', πs)                   = splitRPvar π r2
    isPredInReft                = not $ null πs

substPred msg su@(π, _ ) (RApp c ts rs r)
  | null πs                     = t'
  | otherwise                   = substRCon msg su t' πs r2'
  where
    t'                          = RApp c (substPred msg su <$> ts) (substPredP msg su <$> rs) r
    (r2', πs)                   = splitRPvar π r

substPred msg (p, tp) (RAllP (q@(PV _ _ _ _)) t)
  | p /= q                      = RAllP q $ substPred msg (p, tp) t
  | otherwise                   = RAllP q t

substPred msg su (RAllT a t)    = RAllT a (substPred msg su t)

substPred msg su@(π,prop) (RFun x t t' r)
--                        = RFun x (substPred msg su t) (substPred msg su t') r
  | null πs                     = RFun x (substPred msg su t) (substPred msg su t') r
  | otherwise                   =
      let sus = (\π -> F.mkSubst (zip (fst <$> rf_args prop) (thd3 <$> pargs π))) <$> πs in
      foldl (\t su -> t `F.meet` F.subst su (rf_body prop)) (RFun x (substPred msg su t) (substPred msg su t') r') sus
  where (r', πs)                = splitRPvar π r
-- ps has   , pargs :: ![(t, Symbol, Expr)]


substPred msg su (RRTy e r o t) = RRTy (mapSnd (substPred msg su) <$> e) r o (substPred msg su t)
substPred msg su (RAllE x t t') = RAllE x (substPred msg su t) (substPred msg su t')
substPred msg su (REx x t t')   = REx   x (substPred msg su t) (substPred msg su t')
substPred _   _  t              = t

-- | Requires: @not $ null πs@
-- substRCon :: String -> (RPVar, SpecType) -> SpecType -> SpecType

substRCon
  :: (PPrint t, PPrint t2, Eq tv, F.Reftable r, Hashable tv, PPrint tv, PPrint r,
      SubsTy tv (RType RTyCon tv ()) r,
      SubsTy tv (RType RTyCon tv ()) (RType RTyCon tv ()),
      SubsTy tv (RType RTyCon tv ()) RTyCon,
      SubsTy tv (RType RTyCon tv ()) tv,
      F.Reftable (RType RTyCon tv r),
      SubsTy tv (RType RTyCon tv ()) (RTVar tv (RType RTyCon tv ())),
      FreeVar RTyCon tv,
      F.Reftable (RTProp RTyCon tv r),
      F.Reftable (RTProp RTyCon tv ()))
  => [Char]
  -> (t, Ref RSort (RType RTyCon tv r))
  -> RType RTyCon tv r
  -> [PVar t2]
  -> r
  -> RType RTyCon tv r
substRCon msg (_, RProp ss t1@(RApp c1 ts1 rs1 r1)) t2@(RApp c2 ts2 rs2 _) πs r2'
  | rtc_tc c1 == rtc_tc c2 = RApp c1 ts rs $ meetListWithPSubs πs ss r1 r2'
  where
    ts                     = F.subst su $ safeZipWith (msg ++ ": substRCon")  strSub  ts1  ts2
    rs                     = F.subst su $ safeZipWith (msg ++ ": substRCon2") strSubR rs1' rs2'
    (rs1', rs2')           = pad "substRCon" F.top rs1 rs2
    strSub r1 r2           = meetListWithPSubs πs ss r1 r2
    strSubR r1 r2          = meetListWithPSubsRef πs ss r1 r2

    su = F.mkSubst $ zipWith (\s1 s2 -> (s1, F.EVar s2)) (rvs t1) (rvs t2)

    rvs      = foldReft (\_ r acc -> rvReft r : acc) []
    rvReft r = let F.Reft(s,_) = F.toReft r in s

substRCon msg su t _ _        = panic Nothing $ msg ++ " substRCon " ++ showpp (su, t)

pad :: [Char] -> (a -> a) -> [a] -> [a] -> ([a], [a])
pad _ f [] ys   = (f <$> ys, ys)
pad _ f xs []   = (xs, f <$> xs)
pad msg _ xs ys
  | nxs == nys  = (xs, ys)
  | otherwise   = panic Nothing $ "pad: " ++ msg
  where
    nxs         = length xs
    nys         = length ys

substPredP :: [Char]
           -> (RPVar, Ref RSort (RRType RReft))
           -> Ref RSort (RType RTyCon RTyVar RReft)
           -> Ref RSort SpecType
substPredP _ su p@(RProp _ (RHole _))
  = panic Nothing ("PredType.substPredP1 called on invalid inputs: " ++ showpp (su, p))
substPredP msg (p, RProp ss prop) (RProp s t)
  = RProp ss' $ substPred (msg ++ ": substPredP") (p, RProp ss {- (subst su prop) -} prop ) t
 where
   ss' = drop n ss ++  s
   n   = length ss - length (freeArgsPs p t)
   -- su  = mkSubst (zip (fst <$> ss) (EVar . fst <$> ss'))


splitRPvar :: PVar t -> UReft r -> (UReft r, [UsedPVar])
splitRPvar pv (MkUReft x (Pr pvs) s) = (MkUReft x (Pr pvs') s, epvs)
  where
    (epvs, pvs')               = partition (uPVar pv ==) pvs

-- TODO: rewrite using foldReft
freeArgsPs :: PVar (RType t t1 ()) -> RType t t1 (UReft t2) -> [F.Symbol]
freeArgsPs p (RVar _ r)
  = freeArgsPsRef p r
freeArgsPs p (RFun _ t1 t2 r)
  = nub $  freeArgsPsRef p r ++ freeArgsPs p t1 ++ freeArgsPs p t2
freeArgsPs p (RAllT _ t)
  = freeArgsPs p t
freeArgsPs p (RAllS _ t)
  = freeArgsPs p t
freeArgsPs p (RAllP p' t)
  | p == p'   = []
  | otherwise = freeArgsPs p t
freeArgsPs p (RApp _ ts _ r)
  = nub $ freeArgsPsRef p r ++ concatMap (freeArgsPs p) ts
freeArgsPs p (RAllE _ t1 t2)
  = nub $ freeArgsPs p t1 ++ freeArgsPs p t2
freeArgsPs p (REx _ t1 t2)
  = nub $ freeArgsPs p t1 ++ freeArgsPs p t2
freeArgsPs p (RAppTy t1 t2 r)
  = nub $ freeArgsPsRef p r ++ freeArgsPs p t1 ++ freeArgsPs p t2
freeArgsPs _ (RExprArg _)
  = []
freeArgsPs p (RHole r)
  = freeArgsPsRef p r
freeArgsPs p (RRTy env r _ t)
  = nub $ concatMap (freeArgsPs p) (snd <$> env) ++ freeArgsPsRef p r ++ freeArgsPs p t

freeArgsPsRef :: PVar t1 -> UReft t -> [F.Symbol]
freeArgsPsRef p (MkUReft _ (Pr ps) _) = [x | (_, x, w) <- (concatMap pargs ps'),  (F.EVar x) == w]
  where
   ps' = f <$> filter (uPVar p ==) ps
   f q = q {pargs = pargs q ++ drop (length (pargs q)) (pargs $ uPVar p)}

meetListWithPSubs :: (Foldable t, PPrint t1, F.Reftable b)
                  => t (PVar t1) -> [(F.Symbol, RSort)] -> b -> b -> b
meetListWithPSubs πs ss r1 r2    = foldl' (meetListWithPSub ss r1) r2 πs

meetListWithPSubsRef :: (Foldable t, F.Reftable (RType t1 t2 t3))
                     => t (PVar t4)
                     -> [(F.Symbol, b)]
                     -> Ref τ (RType t1 t2 t3)
                     -> Ref τ (RType t1 t2 t3)
                     -> Ref τ (RType t1 t2 t3)
meetListWithPSubsRef πs ss r1 r2 = foldl' ((meetListWithPSubRef ss) r1) r2 πs

meetListWithPSub ::  (F.Reftable r, PPrint t) => [(F.Symbol, RSort)]-> r -> r -> PVar t -> r
meetListWithPSub ss r1 r2 π
  | all (\(_, x, F.EVar y) -> x == y) (pargs π)
  = r2 `F.meet` r1
  | all (\(_, x, F.EVar y) -> x /= y) (pargs π)
  = r2 `F.meet` (F.subst su r1)
  | otherwise
  = panic Nothing $ "PredType.meetListWithPSub partial application to " ++ showpp π
  where
    su  = F.mkSubst [(x, y) | (x, (_, _, y)) <- zip (fst <$> ss) (pargs π)]

meetListWithPSubRef :: (F.Reftable (RType t t1 t2))
                    => [(F.Symbol, b)]
                    -> Ref τ (RType t t1 t2)
                    -> Ref τ (RType t t1 t2)
                    -> PVar t3
                    -> Ref τ (RType t t1 t2)
meetListWithPSubRef _ (RProp _ (RHole _)) _ _ -- TODO: Is this correct?
  = panic Nothing "PredType.meetListWithPSubRef called with invalid input"
meetListWithPSubRef _ _ (RProp _ (RHole _)) _
  = panic Nothing "PredType.meetListWithPSubRef called with invalid input"
meetListWithPSubRef ss (RProp s1 r1) (RProp s2 r2) π
  | all (\(_, x, F.EVar y) -> x == y) (pargs π)
  = RProp s1 $ (F.subst su' r2) `F.meet` r1
  | all (\(_, x, F.EVar y) -> x /= y) (pargs π)
  = RProp s2 $ r2 `F.meet` (F.subst su r1)
  | otherwise
  = panic Nothing $ "PredType.meetListWithPSubRef partial application to " ++ showpp π
  where
    su  = F.mkSubst [(x, y) | (x, (_, _, y)) <- zip (fst <$> ss) (pargs π)]
    su' = F.mkSubst [(x, F.EVar y) | (x, y) <- zip (fst <$> s2) (fst <$> s1)]


----------------------------------------------------------------------------
-- | Interface: Modified CoreSyn.exprType due to predApp -------------------
----------------------------------------------------------------------------
predType   :: Type
predType   = symbolType predName

wpredName, predName :: F.Symbol
predName   = "Pred"
wpredName  = "WPred"

symbolType :: F.Symbol -> Type
symbolType = TyVarTy . symbolTyVar


substParg :: Functor f => (F.Symbol, F.Expr) -> f Predicate -> f Predicate
substParg (x, y) = fmap fp
  where
    fxy s        = if (s == F.EVar x) then y else s
    fp           = subvPredicate (\pv -> pv { pargs = mapThd3 fxy <$> pargs pv })

-------------------------------------------------------------------------------
-----------------------------  Predicate Application --------------------------
-------------------------------------------------------------------------------
pappArity :: Int
pappArity  = 7

pappSort :: Int -> F.Sort
pappSort n = F.mkFFunc (2 * n) $ [ptycon] ++ args ++ [F.boolSort]
  where
    ptycon = F.fAppTC predFTyCon $ F.FVar <$> [0..n-1]
    args   = F.FVar <$> [n..(2*n-1)]


predFTyCon :: F.FTycon
predFTyCon = F.symbolFTycon $ dummyLoc predName
