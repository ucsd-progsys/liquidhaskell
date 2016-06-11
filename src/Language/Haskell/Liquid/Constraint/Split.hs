{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}

--------------------------------------------------------------------------------
-- | Constraint Splitting ------------------------------------------------------
--------------------------------------------------------------------------------

module Language.Haskell.Liquid.Constraint.Split (

  -- * Split Subtyping Constraints
    splitC

  -- * Split Well-formedness Constraints
  , splitW

  -- * Split Strata Constraints
  , splitS

  -- * ???
  , envToSub

  -- * Panic
  , panicUnbound
  ) where

import           Prelude hiding (error)



import           Text.PrettyPrint.HughesPJ hiding (first)
import qualified TyCon  as TC

import           Data.Maybe          (fromMaybe) -- catMaybes, fromJust, isJust)
import           Control.Monad
import           Control.Monad.State (get)
import qualified Control.Exception as Ex

import qualified Language.Fixpoint.Types            as F
import           Language.Fixpoint.Misc hiding (errorstar)
import           Language.Fixpoint.SortCheck (pruneUnsortedReft)

import           Language.Haskell.Liquid.Misc -- (concatMapM)
import qualified Language.Haskell.Liquid.UX.CTags       as Tg
import           Language.Haskell.Liquid.UX.Errors () -- CTags       as Tg
import           Language.Haskell.Liquid.Types hiding (loc)

import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Strata
import           Language.Haskell.Liquid.Types.PredType         hiding (freeTyVars)
import           Language.Haskell.Liquid.Types.RefType

import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.Fresh
import           Language.Haskell.Liquid.Constraint.Monad
import           Language.Haskell.Liquid.Constraint.Constraint

--------------------------------------------------------------------------------
splitW ::  WfC -> CG [FixWfC]
--------------------------------------------------------------------------------
splitW (WfC γ t@(RFun x t1 t2 _))
  =  do ws'  <- splitW (WfC γ t1)
        γ'   <- (γ, "splitW") += (x, t1)
        ws   <- bsplitW γ t
        ws'' <- splitW (WfC γ' t2)
        return $ ws ++ ws' ++ ws''

splitW (WfC γ t@(RAppTy t1 t2 _))
  =  do ws   <- bsplitW γ t
        ws'  <- splitW (WfC γ t1)
        ws'' <- splitW (WfC γ t2)
        return $ ws ++ ws' ++ ws''

splitW (WfC γ (RAllT _ r))
  = splitW (WfC γ r)

splitW (WfC γ (RAllP _ r))
  = splitW (WfC γ r)

splitW (WfC γ t@(RVar _ _))
  = bsplitW γ t

splitW (WfC γ t@(RApp _ ts rs _))
  =  do ws    <- bsplitW γ t
        γ'    <- γ `extendEnvWithVV` t
        ws'   <- concat <$> mapM (splitW . WfC γ') ts
        ws''  <- concat <$> mapM (rsplitW γ)       rs
        return $ ws ++ ws' ++ ws''

splitW (WfC γ (RAllE x tx t))
  = do  ws  <- splitW (WfC γ tx)
        γ'  <- (γ, "splitW") += (x, tx)
        ws' <- splitW (WfC γ' t)
        return $ ws ++ ws'

splitW (WfC γ (REx x tx t))
  = do  ws  <- splitW (WfC γ tx)
        γ'  <- (γ, "splitW") += (x, tx)
        ws' <- splitW (WfC γ' t)
        return $ ws ++ ws'

splitW (WfC _ t)
  = panic Nothing $ "splitW cannot handle: " ++ showpp t

rsplitW :: CGEnv
        -> Ref RSort SpecType
        -> CG [FixWfC]
rsplitW _ (RProp _ (RHole _))
  = panic Nothing "Constrains: rsplitW for RProp _ (RHole _)"
rsplitW γ (RProp ss t0)
  = do γ' <- foldM (++=) γ [("rsplitW", x, ofRSort s) | (x, s) <- ss]
       splitW $ WfC γ' t0

bsplitW :: CGEnv -> SpecType -> CG [FixWfC]
bsplitW γ t =
  do pflag <- pruneRefs <$> get
     isHO  <- allowHO   <$> get
     return $ bsplitW' γ t pflag isHO

bsplitW' :: (PPrint r, F.Reftable r, SubsTy RTyVar RSort r)
         => CGEnv -> RRType r -> Bool -> Bool -> [F.WfC Cinfo]
bsplitW' γ t pflag isHO
  | isHO || F.isNonTrivial r'
  = F.wfC (feBinds $ fenv γ) r' ci
  | otherwise
  = []
  where
    r'                = rTypeSortedReft' pflag γ t
    ci                = Ci (getLocation γ) Nothing

--------------------------------------------------------------------------------
splitS  :: SubC -> CG [([Stratum], [Stratum])]
bsplitS :: SpecType -> SpecType -> CG [([Stratum], [Stratum])]
--------------------------------------------------------------------------------
splitS (SubC γ (REx x _ t1) (REx x2 _ t2)) | x == x2
  = splitS (SubC γ t1 t2)

splitS (SubC γ t1 (REx _ _ t2))
  = splitS (SubC γ t1 t2)

splitS (SubC γ (REx _ _ t1) t2)
  = splitS (SubC γ t1 t2)

splitS (SubC γ (RAllE x _ t1) (RAllE x2 _ t2)) | x == x2
  = splitS (SubC γ t1 t2)

splitS (SubC γ (RAllE _ _ t1) t2)
  = splitS (SubC γ t1 t2)

splitS (SubC γ t1 (RAllE _ _ t2))
  = splitS (SubC γ t1 t2)

splitS (SubC γ (RRTy _ _ _ t1) t2)
  = splitS (SubC γ t1 t2)

splitS (SubC γ t1 (RRTy _ _ _ t2))
  = splitS (SubC γ t1 t2)

splitS (SubC γ t1@(RFun x1 r1 r1' _) t2@(RFun x2 r2 r2' _))
  =  do cs       <- bsplitS t1 t2
        cs'      <- splitS  (SubC γ r2 r1)
        γ'       <- (γ, "splitS") += (x2, r2)
        let r1x2' = r1' `F.subst1` (x1, F.EVar x2)
        cs''     <- splitS  (SubC γ' r1x2' r2')
        return    $ cs ++ cs' ++ cs''

splitS (SubC γ t1@(RAppTy r1 r1' _) t2@(RAppTy r2 r2' _))
  =  do cs    <- bsplitS t1 t2
        cs'   <- splitS  (SubC γ r1 r2)
        cs''  <- splitS  (SubC γ r1' r2')
        cs''' <- splitS  (SubC γ r2' r1')
        return $ cs ++ cs' ++ cs'' ++ cs'''

splitS (SubC γ t1 (RAllP p t))
  = splitS $ SubC γ t1 t'
  where
    t' = fmap (replacePredsWithRefs su) t
    su = (uPVar p, pVartoRConc p)

splitS (SubC _ t1@(RAllP _ _) t2)
  = panic Nothing $ "Predicate in lhs of constrain:" ++ showpp t1 ++ "\n<:\n" ++ showpp t2

splitS (SubC γ (RAllT α1 t1) (RAllT α2 t2))
  |  α1 ==  α2
  = splitS $ SubC γ t1 t2
  | otherwise
  = splitS $ SubC γ t1 t2'
  where t2' = subsTyVar_meet' (α2, RVar α1 mempty) t2

splitS (SubC _ (RApp c1 _ _ _) (RApp c2 _ _ _)) | isClass c1 && c1 == c2
  = return []


splitS (SubC γ t1@(RApp {}) t2@(RApp {}))
  = do (t1',t2') <- unifyVV t1 t2
       cs    <- bsplitS t1' t2'
       γ'    <- γ `extendEnvWithVV` t1'
       let RApp c t1s r1s _ = t1'
       let RApp _ t2s r2s _ = t2'
       let isapplied = TC.tyConArity (rtc_tc c) == length t1s
       let tyInfo = rtc_info c
       csvar  <-  splitsSWithVariance           γ' t1s t2s $ varianceTyArgs tyInfo
       csvar' <- rsplitsSWithVariance isapplied γ' r1s r2s $ variancePsArgs tyInfo
       return $ cs ++ csvar ++ csvar'

splitS (SubC _ t1@(RVar a1 _) t2@(RVar a2 _))
  | a1 == a2
  = bsplitS t1 t2

splitS (SubC _ t1 t2)
  = panic Nothing $ "(Another Broken Test1!!!) splitS unexpected: " ++ showpp t1 ++ "\n\n" ++ showpp t2

splitS (SubR _ _ _)
  = return []

splitsSWithVariance :: CGEnv
                    -> [SpecType]
                    -> [SpecType]
                    -> [Variance]
                    -> CG [([Stratum], [Stratum])]
splitsSWithVariance γ t1s t2s variants
  = concatMapM (\(t1, t2, v) -> splitfWithVariance (\s1 s2 -> splitS (SubC γ s1 s2)) t1 t2 v) (zip3 t1s t2s variants)

rsplitsSWithVariance :: Bool
                     -> CGEnv
                     -> [Ref t (RType RTyCon RTyVar RReft)]
                     -> [Ref t (RType RTyCon RTyVar RReft)]
                     -> [Variance]
                     -> CG [([Stratum], [Stratum])]
rsplitsSWithVariance False _ _ _ _
  = return []

rsplitsSWithVariance _ γ t1s t2s variants
  = concatMapM (\(t1, t2, v) -> splitfWithVariance (rsplitS γ) t1 t2 v) (zip3 t1s t2s variants)

bsplitS t1 t2
  = return $ [(s1, s2)]
  where [s1, s2]   = getStrata <$> [t1, t2]

rsplitS :: CGEnv
        -> Ref t (RType RTyCon RTyVar RReft)
        -> Ref t1 (RType RTyCon RTyVar RReft)
        -> CG [([Stratum], [Stratum])]
rsplitS _ (RProp _ (RHole _)) _
   = panic Nothing "rsplitS RProp _ (RHole _)"

rsplitS _ _ (RProp _ (RHole _))
   = panic Nothing "rsplitS RProp _ (RHole _)"

rsplitS γ (RProp s1 r1) (RProp s2 r2)
  = splitS (SubC γ (F.subst su r1) r2)
  where su = F.mkSubst [(x, F.EVar y) | ((x,_), (y,_)) <- zip s1 s2]

splitfWithVariance :: Applicative f
                   => (t -> t -> f [a]) -> t -> t -> Variance -> f [a]
splitfWithVariance f t1 t2 Invariant     = (++) <$> f t1 t2 <*> f t2 t1
splitfWithVariance f t1 t2 Bivariant     = (++) <$> f t1 t2 <*> f t2 t1
splitfWithVariance f t1 t2 Covariant     = f t1 t2
splitfWithVariance f t1 t2 Contravariant = f t2 t1


------------------------------------------------------------
splitC :: SubC -> CG [FixSubC]
------------------------------------------------------------

splitC (SubC γ (REx x tx t1) (REx x2 _ t2)) | x == x2
  = do γ' <- (γ, "addExBind 0") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ t1 (REx x tx t2))
  = do y <- fresh
       γ' <- (γ, "addExBind 1") += (y, forallExprRefType γ tx)
       splitC (SubC γ' t1 (F.subst1 t2 (x, F.EVar y)))

-- existential at the left hand side is treated like forall
splitC (SubC γ (REx x tx t1) t2)
  = do -- let tx' = traceShow ("splitC: " ++ showpp z) tx
       y <- fresh
       γ' <- (γ, "addExBind 2") += (y, forallExprRefType γ tx)
       splitC (SubC γ' (F.subst1 t1 (x, F.EVar y)) t2)

splitC (SubC γ (RAllE x tx t1) (RAllE x2 _ t2)) | x == x2
  = do γ' <- (γ, "addAllBind 0") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ (RAllE x tx t1) t2)
  = do y  <- fresh
       γ' <- (γ, "addAABind 1") += (y, forallExprRefType γ tx)
       splitC (SubC γ' (t1 `F.subst1` (x, F.EVar y)) t2)

splitC (SubC γ t1 (RAllE x tx t2))
  = do y  <- fresh
       γ' <- (γ, "addAllBind 2") += (y, forallExprRefType γ tx)
       splitC (SubC γ' t1 (F.subst1 t2 (x, F.EVar y)))

splitC (SubC γ (RRTy env _ OCons t1) t2)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("splitS", x,t)) γ xts
       c1 <- splitC (SubC γ' t1' t2')
       c2 <- splitC (SubC γ  t1  t2 )
       return $ c1 ++ c2
  where
    (xts, t1', t2') = envToSub env

splitC (SubC γ (RRTy e r o t1) t2)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("splitS", x,t)) γ e
       c1 <- splitC (SubR γ' o  r)
       c2 <- splitC (SubC γ t1 t2)
       return $ c1 ++ c2

splitC (SubC γ (RFun x1 t1 t1' r1) (RFun x2 t2 t2' r2))
  =  do cs'      <- splitC  (SubC γ t2 t1)
        γ'       <- (γ, "splitC") += (x2, t2)
        cs       <- bsplitC γ (RFun x1 t1 t1' (r1 `F.subst1` (x1, F.EVar x2))) 
                              (RFun x2 t2 t2'  r2)
        let t1x2' = t1' `F.subst1` (x1, F.EVar x2)
        cs''     <- splitC  (SubC γ' t1x2' t2')
        return    $ cs ++ cs' ++ cs''

splitC (SubC γ t1@(RAppTy r1 r1' _) t2@(RAppTy r2 r2' _))
  =  do cs    <- bsplitC γ t1 t2
        cs'   <- splitC  (SubC γ r1 r2)
        cs''  <- splitC  (SubC γ r1' r2')
        cs''' <- splitC  (SubC γ r2' r1')
        return $ cs ++ cs' ++ cs'' ++ cs'''

splitC (SubC γ t1 (RAllP p t))
  = splitC $ SubC γ t1 t'
  where
    t' = fmap (replacePredsWithRefs su) t
    su = (uPVar p, pVartoRConc p)

splitC (SubC γ t1@(RAllP _ _) t2)
  = panic (Just $ getLocation γ) $ "Predicate in lhs of constraint:" ++ showpp t1 ++ "\n<:\n" ++ showpp t2

splitC (SubC γ (RAllT α1 t1) (RAllT α2 t2))
  |  α1 ==  α2
  = splitC $ SubC γ t1 t2
  | otherwise
  = splitC $ SubC γ t1 t2'
  where t2' = subsTyVar_meet' (α2, RVar α1 mempty) t2


splitC (SubC _ (RApp c1 _ _ _) (RApp c2 _ _ _)) | isClass c1 && c1 == c2
  = return []

splitC (SubC γ t1@(RApp _ _ _ _) t2@(RApp _ _ _ _))
  = do (t1',t2') <- unifyVV t1 t2
       cs    <- bsplitC γ t1' t2'
       γ'    <- γ `extendEnvWithVV` t1'
       let RApp c t1s r1s _ = t1'
       let RApp _ t2s r2s _ = t2'
       let isapplied = True -- TC.tyConArity (rtc_tc c) == length t1s
       let tyInfo = rtc_info c
       csvar  <-  splitsCWithVariance           γ' t1s t2s $ varianceTyArgs tyInfo
       csvar' <- rsplitsCWithVariance isapplied γ' r1s r2s $ variancePsArgs tyInfo
       return $ cs ++ csvar ++ csvar'

splitC (SubC γ t1@(RVar a1 _) t2@(RVar a2 _))
  | a1 == a2
  = bsplitC γ t1 t2

splitC (SubC _ t1 t2)
  = panic Nothing $ "(Another Broken Test!!!) splitc unexpected:\n" ++ showpp t1 ++ "\n  <:\n" ++ showpp t2

splitC (SubR γ o r)
  = do fg     <- pruneRefs <$> get
       let r1' = if fg then pruneUnsortedReft γ'' r1 else r1
       return $ F.subC γ' r1' r2 Nothing tag ci
  where
    γ'' = feEnv $ fenv γ
    γ'  = feBinds $ fenv γ
    r1  = F.RR F.boolSort rr
    r2  = F.RR F.boolSort $ F.Reft (vv, F.EVar vv)
    vv  = "vvRec"
    ci  = Ci src err
    err = Just $ ErrAssType src o (text $ show o ++ "type error") g (rHole rr)
    rr  = F.toReft r
    tag = getTag γ
    src = getLocation γ
    g   = reLocal $ renv γ

rHole :: F.Reft -> SpecType
rHole = RHole . uTop


splitsCWithVariance :: CGEnv
                    -> [SpecType]
                    -> [SpecType]
                    -> [Variance]
                    -> CG [FixSubC]
splitsCWithVariance γ t1s t2s variants
  = concatMapM (\(t1, t2, v) -> splitfWithVariance (\s1 s2 -> (splitC (SubC γ s1 s2))) t1 t2 v) (zip3 t1s t2s variants)

rsplitsCWithVariance :: Bool
                     -> CGEnv
                     -> [SpecProp]
                     -> [SpecProp]
                     -> [Variance]
                     -> CG [FixSubC]
rsplitsCWithVariance False _ _ _ _
  = return []

rsplitsCWithVariance _ γ t1s t2s variants
  = concatMapM (\(t1, t2, v) -> splitfWithVariance (rsplitC γ) t1 t2 v) (zip3 t1s t2s variants)

bsplitC :: CGEnv
        -> SpecType
        -> SpecType
        -> CG [F.SubC Cinfo]
bsplitC γ t1 t2 = do
  checkStratum γ t1 t2
  pflag  <- pruneRefs <$> get
  isHO   <- allowHO   <$> get
  let t1' = addLhsInv γ t1
  return  $ bsplitC' γ t1' t2 pflag isHO

addLhsInv :: CGEnv -> SpecType -> SpecType
addLhsInv γ t = addRTyConInv (invs γ) t `strengthen` r
  where
    r         = (mempty :: UReft F.Reft) { ur_reft = F.Reft (F.dummySymbol, p) }
    p         = constraintToLogic rE' (lcs γ)
    rE'       = insertREnv v t (renv γ)
    v         = rTypeValueVar t

     -- γ'     <- γ ++= ("bsplitC", v, t1)
       -- let r   = (mempty :: UReft F.Reft){ur_reft = F.Reft (F.dummySymbol, constraintToLogic γ' (lcs γ'))}
       -- let t1' = addRTyConInv (invs γ')  t1 `strengthen` r
       -- let F.Reft(v, _) = ur_reft (fromMaybe mempty (stripRTypeBase t1))

checkStratum :: CGEnv
             -> RType t t1 (UReft r)
             -> RType t t1 (UReft r)
             -> CG ()
checkStratum γ t1 t2
  | s1 <:= s2 = return ()
  | otherwise = addWarning wrn
  where
    [s1, s2]  = getStrata <$> [t1, t2]
    wrn       =  ErrOther (getLocation γ) (text $ "Stratum Error : " ++ show s1 ++ " > " ++ show s2)

bsplitC' :: CGEnv -> SpecType -> SpecType -> Bool -> Bool -> [F.SubC Cinfo]
bsplitC' γ t1 t2 pflag isHO
 | isHO
 = F.subC γ' r1'  r2' Nothing tag ci
 | F.isFunctionSortedReft r1' && F.isNonTrivial r2'
 = F.subC γ' (r1' {F.sr_reft = mempty}) r2' Nothing tag ci
 | F.isNonTrivial r2'
 = F.subC γ' r1'  r2' Nothing tag ci
 | otherwise
 = []
  where
    γ'  = feBinds $ fenv γ
    r1' = rTypeSortedReft' pflag γ t1
    r2' = rTypeSortedReft' pflag γ t2
    ci  = Ci src err
    tag = getTag γ
    -- err = Just $ ErrSubType src "subtype" g t1 t2
    err = Just $ fromMaybe (ErrSubType src (text "subtype") g t1 t2) (cerr γ)
    src = getLocation γ
    g   = reLocal $ renv γ

unifyVV :: SpecType -> SpecType -> CG (SpecType, SpecType)
unifyVV t1@(RApp _ _ _ _) t2@(RApp _ _ _ _)
  = do vv     <- (F.vv . Just) <$> fresh
       return  $ (shiftVV t1 vv,  (shiftVV t2 vv) )

unifyVV _ _
  = panic Nothing $ "Constraint.Generate.unifyVV called on invalid inputs"

rsplitC :: CGEnv
        -> SpecProp
        -> SpecProp
        -> CG [FixSubC]
rsplitC _ _ (RProp _ (RHole _))
  = panic Nothing "RefTypes.rsplitC on RProp _ (RHole _)"

rsplitC _ (RProp _ (RHole _)) _
  = panic Nothing "RefTypes.rsplitC on RProp _ (RHole _)"

rsplitC γ (RProp s1 r1) (RProp s2 r2)
  = do γ'  <-  foldM (++=) γ [("rsplitC1", x, ofRSort s) | (x, s) <- s2]
       splitC (SubC γ' (F.subst su r1) r2)
  where su = F.mkSubst [(x, F.EVar y) | ((x,_), (y,_)) <- zip s1 s2]


--------------------------------------------------------------------------------
-- | Reftypes from F.Fixpoint Expressions --------------------------------------
--------------------------------------------------------------------------------
forallExprRefType     :: CGEnv -> SpecType -> SpecType
forallExprRefType γ t = t `strengthen` (uTop r')
  where
    r'                = fromMaybe mempty $ forallExprReft γ r
    r                 = F.sr_reft $ rTypeSortedReft (emb γ) t

forallExprReft :: CGEnv -> F.Reft -> Maybe F.Reft
forallExprReft γ r =
  do e <- F.isSingletonReft r
     forallExprReft_ γ $ F.splitEApp e

forallExprReft_ :: CGEnv -> (F.Expr, [F.Expr]) -> Maybe F.Reft
forallExprReft_ γ (F.EVar x, [])
  = case forallExprReftLookup γ x of
      Just (_,_,_,t)  -> Just $ F.sr_reft $ rTypeSortedReft (emb γ) t
      Nothing         -> Nothing

forallExprReft_ γ (F.EVar f, es)
  = case forallExprReftLookup γ f of
      Just (xs,_,_,t) -> let su = F.mkSubst $ safeZip "fExprRefType" xs es in
                       Just $ F.subst su $ F.sr_reft $ rTypeSortedReft (emb γ) t
      Nothing       -> Nothing

forallExprReft_ _ _
  = Nothing

-- forallExprReftLookup :: CGEnv -> F.Symbol -> Int
forallExprReftLookup :: CGEnv
                     -> F.Symbol
                     -> Maybe ([F.Symbol], [SpecType], [RReft], SpecType)
forallExprReftLookup γ x = snap <$> F.lookupSEnv x (syenv γ)
  where
    snap     = mapFourth4 ignoreOblig . bkArrow . fourth4 . bkUniv . lookup
    lookup z = fromMaybe (panicUnbound γ z) (γ ?= F.symbol z)


--------------------------------------------------------------------------------
getTag :: CGEnv -> F.Tag
--------------------------------------------------------------------------------
getTag γ = maybe Tg.defaultTag (`Tg.getTag` tgEnv γ) (tgKey γ)


--------------------------------------------------------------------------------
{-@ envToSub :: {v:[(a, b)] | 2 <= len v} -> ([(a, b)], b, b) @-}
envToSub :: [(a, b)] -> ([(a, b)], b, b)
--------------------------------------------------------------------------------
envToSub = go []
  where
    go _   []              = impossible Nothing "This cannot happen: envToSub on 0 elems"
    go _   [(_,_)]         = impossible Nothing "This cannot happen: envToSub on 1 elem"
    go ack [(_,l), (_, r)] = (reverse ack, l, r)
    go ack (x:xs)          = go (x:ack) xs

--------------------------------------------------------------------------------
-- | Constraint Generation Panic -----------------------------------------------
--------------------------------------------------------------------------------
panicUnbound :: (PPrint x) => CGEnv -> x -> a
panicUnbound γ x = Ex.throw $ (ErrUnbound (getLocation γ) (F.pprint x) :: Error)
