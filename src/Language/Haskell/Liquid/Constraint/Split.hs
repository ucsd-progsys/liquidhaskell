{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts      #-}

--------------------------------------------------------------------------------
-- | Constraint Splitting ------------------------------------------------------
--------------------------------------------------------------------------------

module Language.Haskell.Liquid.Constraint.Split (

  -- * Split Subtyping Constraints
    splitC

  -- * Split Well-formedness Constraints
  , splitW

  -- * ???
  , envToSub

  -- * Panic
  , panicUnbound
  ) where

import           Prelude hiding (error)



import           Text.PrettyPrint.HughesPJ hiding (first, parens)

import           Data.Maybe          (fromMaybe) 
import           Control.Monad
import           Control.Monad.State (get)
import qualified Control.Exception as Ex

import qualified Language.Fixpoint.Types            as F
import           Language.Fixpoint.Misc hiding (errorstar)
import           Language.Fixpoint.SortCheck (pruneUnsortedReft)

import           Language.Haskell.Liquid.Misc -- (concatMapM)
import qualified Language.Haskell.Liquid.UX.CTags       as Tg
import           Language.Haskell.Liquid.Types hiding (loc)


import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.Constraint
import           Language.Haskell.Liquid.Constraint.Monad (envToSub)

--------------------------------------------------------------------------------
splitW ::  WfC -> CG [FixWfC]
--------------------------------------------------------------------------------
splitW (WfC γ t@(RFun x _ t1 t2 _))
  =  do ws'  <- splitW (WfC γ t1)
        γ'   <- γ += ("splitW", x, t1)
        ws   <- bsplitW γ t
        ws'' <- splitW (WfC γ' t2)
        return $ ws ++ ws' ++ ws''

splitW (WfC γ t@(RImpF x _ t1 t2 _))
  =  do ws'  <- splitW (WfC γ t1)
        γ'   <- γ += ("splitW", x, t1)
        ws   <- bsplitW γ t
        ws'' <- splitW (WfC γ' t2)
        return $ ws ++ ws' ++ ws''


splitW (WfC γ t@(RAppTy t1 t2 _))
  =  do ws   <- bsplitW γ t
        ws'  <- splitW (WfC γ t1)
        ws'' <- splitW (WfC γ t2)
        return $ ws ++ ws' ++ ws''

splitW (WfC γ t'@(RAllT a t _))
  = do γ'  <- updateEnv γ a
       ws  <- bsplitW γ t'
       ws' <- splitW (WfC γ' t)
       return $ ws ++ ws'

splitW (WfC γ (RAllP _ r))
  = splitW (WfC γ r)

splitW (WfC γ t@(RVar _ _))
  = bsplitW γ t

splitW (WfC γ t@(RApp _ ts rs _))
  =  do ws    <- bsplitW γ t
        γ'    <- if bscope (getConfig γ) then γ `extendEnvWithVV` t else return γ
        ws'   <- concat <$> mapM (splitW . WfC γ') ts
        ws''  <- concat <$> mapM (rsplitW γ)       rs
        return $ ws ++ ws' ++ ws''

splitW (WfC γ (RAllE x tx t))
  = do  ws  <- splitW (WfC γ tx)
        γ'  <- γ += ("splitW1", x, tx)
        ws' <- splitW (WfC γ' t)
        return $ ws ++ ws'

splitW (WfC γ (REx x tx t))
  = do  ws  <- splitW (WfC γ tx)
        γ'  <- γ += ("splitW2", x, tx)
        ws' <- splitW (WfC γ' t)
        return $ ws ++ ws'

splitW (WfC γ (RRTy _ _ _ t))
  = splitW (WfC γ t) 

splitW (WfC _ t)
  = panic Nothing $ "splitW cannot handle: " ++ showpp t

rsplitW :: CGEnv
        -> Ref RSort SpecType
        -> CG [FixWfC]
rsplitW _ (RProp _ (RHole _)) =
  panic Nothing "Constrains: rsplitW for RProp _ (RHole _)"

rsplitW γ (RProp ss t0) = do
  γ' <- foldM (+=) γ [("rsplitW", x, ofRSort s) | (x, s) <- ss]
  splitW $ WfC γ' t0


bsplitW :: CGEnv -> SpecType -> CG [FixWfC]
bsplitW γ t =
  do temp  <- getTemplates
     isHO  <- allowHO   <$> get
     return $ bsplitW' γ t temp isHO

bsplitW' :: (PPrint r, F.Reftable r, SubsTy RTyVar RSort r, F.Reftable (RTProp RTyCon RTyVar r))
         => CGEnv -> RRType r -> F.Templates -> Bool -> [F.WfC Cinfo]
bsplitW' γ t temp isHO
  | isHO || F.isNonTrivial r'
  = F.wfC (feBinds $ fenv γ) r' ci
  | otherwise
  = []
  where
    r'                = rTypeSortedReft' γ temp t
    ci                = Ci (getLocation γ) Nothing (cgVar γ)

splitfWithVariance :: Applicative f
                   => (t -> t -> f [a]) -> t -> t -> Variance -> f [a]
splitfWithVariance f t1 t2 Invariant     = (++) <$> f t1 t2 <*> f t2 t1
splitfWithVariance f t1 t2 Bivariant     = (++) <$> f t1 t2 <*> f t2 t1
splitfWithVariance f t1 t2 Covariant     = f t1 t2
splitfWithVariance f t1 t2 Contravariant = f t2 t1

updateEnv :: CGEnv -> RTVar RTyVar (RType RTyCon RTyVar b0) -> CG CGEnv
updateEnv γ a
  | Just (x, s) <- rTVarToBind a
  = γ += ("splitS RAllT", x, fmap (const mempty) s)
  | otherwise
  = return γ

------------------------------------------------------------
splitC :: Bool -> SubC -> CG [FixSubC]
------------------------------------------------------------

splitC allowTC (SubC γ (REx x tx t1) (REx x2 _ t2)) | x == x2
  = do γ' <- γ += ("addExBind 0", x, forallExprRefType γ tx)
       splitC allowTC (SubC γ' t1 t2)

splitC allowTC (SubC γ t1 (REx x tx t2))
  = do y <- fresh
       γ' <- γ += ("addExBind 1", y, forallExprRefType γ tx)
       splitC allowTC (SubC γ' t1 (F.subst1 t2 (x, F.EVar y)))

-- existential at the left hand side is treated like forall
splitC allowTC (SubC γ (REx x tx t1) t2)
  = do -- let tx' = traceShow ("splitC allowTC: " ++ showpp z) tx
       y <- fresh
       γ' <- γ += ("addExBind 2", y, forallExprRefType γ tx)
       splitC allowTC (SubC γ' (F.subst1 t1 (x, F.EVar y)) t2)

splitC allowTC (SubC γ (RAllE x tx t1) (RAllE x2 _ t2)) | x == x2
  = do γ' <- γ += ("addAllBind 3", x, forallExprRefType γ tx)
       splitC allowTC (SubC γ' t1 t2)

splitC allowTC (SubC γ (RAllE x tx t1) t2)
  = do y  <- fresh
       γ' <- γ += ("addAABind 1", y, forallExprRefType γ tx)
       splitC allowTC (SubC γ' (t1 `F.subst1` (x, F.EVar y)) t2)

splitC allowTC (SubC γ t1 (RAllE x tx t2))
  = do y  <- fresh
       γ' <- γ += ("addAllBind 2", y, forallExprRefType γ tx)
       splitC allowTC (SubC γ' t1 (F.subst1 t2 (x, F.EVar y)))

splitC allowTC (SubC γ (RRTy env _ OCons t1) t2)
  = do γ' <- foldM (\γ2 (x, t) -> γ2 `addSEnv` ("splitS", x,t)) γ xts
       c1 <- splitC allowTC (SubC γ' t1' t2')
       c2 <- splitC allowTC (SubC γ  t1  t2 )
       return $ c1 ++ c2
  where
    (xts, t1', t2') = envToSub env

splitC allowTC (SubC γ (RRTy e r o t1) t2)
  = do γ' <- foldM (\γ2 (x, t) -> γ2 `addSEnv` ("splitS", x,t)) γ e
       c1 <- splitC allowTC (SubR γ' o  r)
       c2 <- splitC allowTC (SubC γ t1 t2)
       return $ c1 ++ c2

splitC allowTC (SubC γ (RFun x1 i1 t1 t1' r1) (RFun x2 i2 t2 t2' r2))
  =  do cs'      <- splitC allowTC  (SubC γ t2 t1)
        γ'       <- γ+= ("splitC allowTC", x2, t2)
        cs       <- bsplitC γ (RFun x1 i1 t1 t1' (r1 `F.subst1` (x1, F.EVar x2)))
                              (RFun x2 i2 t2 t2'  r2)
        let t1x2' = t1' `F.subst1` (x1, F.EVar x2)
        cs''     <- splitC allowTC  (SubC γ' t1x2' t2')
        return    $ cs ++ cs' ++ cs''

splitC allowTC (SubC γ (RImpF x1 i1 t1 t1' r1) (RImpF x2 i2 t2 t2' r2))
  =  do cs'      <- splitC allowTC  (SubC γ t2 t1)
        γ'       <- γ+= ("splitC allowTC", x2, t2)
        cs       <- bsplitC γ (RImpF x1 i1 t1 t1' (r1 `F.subst1` (x1, F.EVar x2)))
                              (RImpF x2 i2 t2 t2'  r2)
        let t1x2' = t1' `F.subst1` (x1, F.EVar x2)
        cs''     <- splitC allowTC  (SubC γ' t1x2' t2')
        return    $ cs ++ cs' ++ cs''


splitC allowTC (SubC γ t1@(RAppTy r1 r1' _) t2@(RAppTy r2 r2' _))
  =  do cs    <- bsplitC γ t1 t2
        cs'   <- splitC allowTC  (SubC γ r1 r2)
        cs''  <- splitC allowTC  (SubC γ r1' r2')
        cs''' <- splitC allowTC  (SubC γ r2' r1')
        return $ cs ++ cs' ++ cs'' ++ cs'''

splitC allowTC (SubC γ t1 (RAllP p t))
  = splitC allowTC $ SubC γ t1 t'
  where
    t' = fmap (replacePredsWithRefs su) t
    su = (uPVar p, pVartoRConc p)

splitC _ (SubC γ t1@(RAllP _ _) t2)
  = panic (Just $ getLocation γ) $ "Predicate in lhs of constraint:" ++ showpp t1 ++ "\n<:\n" ++ showpp t2

splitC allowTC (SubC γ t1'@(RAllT α1 t1 _) t2'@(RAllT α2 t2 _))
  |  α1 ==  α2
  = do γ'  <- updateEnv γ α2
       cs  <- bsplitC γ t1' t2'
       cs' <- splitC allowTC $ SubC γ' t1 (F.subst su t2)
       return (cs ++ cs')
  | otherwise
  = do γ'  <- updateEnv γ α2
       cs  <- bsplitC γ t1' t2'
       cs' <- splitC allowTC $ SubC γ' t1 (F.subst su t2'')
       return (cs ++ cs')
  where
    t2'' = subsTyVar_meet' (ty_var_value α2, RVar (ty_var_value α1) mempty) t2
    su = case (rTVarToBind α1, rTVarToBind α2) of
          (Just (x1, _), Just (x2, _)) -> F.mkSubst [(x1, F.EVar x2)]
          _                            -> F.mkSubst []

splitC allowTC (SubC _ (RApp c1 _ _ _) (RApp c2 _ _ _)) | (if allowTC then isEmbeddedDict else isClass) c1 && c1 == c2
  = return []

splitC _ (SubC γ t1@(RApp _ _ _ _) t2@(RApp _ _ _ _))
  = do (t1',t2') <- unifyVV t1 t2
       cs    <- bsplitC γ t1' t2'
       γ'    <- if (bscope (getConfig γ)) then γ `extendEnvWithVV` t1' else return γ
       let RApp c t1s r1s _ = t1'
       let RApp _ t2s r2s _ = t2'
       let isapplied = True -- TC.tyConArity (rtc_tc c) == length t1s
       let tyInfo = rtc_info c
       csvar  <-  splitsCWithVariance           γ' t1s t2s $ varianceTyArgs tyInfo
       csvar' <- rsplitsCWithVariance isapplied γ' r1s r2s $ variancePsArgs tyInfo
       return $ cs ++ csvar ++ csvar'

splitC _ (SubC γ t1@(RVar a1 _) t2@(RVar a2 _))
  | a1 == a2
  = bsplitC γ t1 t2

splitC _ (SubC γ t1 t2)
  = panic (Just $ getLocation γ) $ "(Another Broken Test!!!) splitc unexpected:\n" ++ traceTy t1 ++ "\n  <:\n" ++ traceTy t2

splitC _ (SubR γ o r)
  = do ts     <- getTemplates
       let r1' = pruneUnsortedReft γ'' ts r1
       return $ F.subC γ' r1' r2 Nothing tag ci
  where
    γ'' = feEnv $ fenv γ
    γ'  = feBinds $ fenv γ
    r1  = F.RR F.boolSort rr
    r2  = F.RR F.boolSort $ F.Reft (vv, F.EVar vv)
    vv  = "vvRec"
    ci  = Ci src err (cgVar γ)
    err = Just $ ErrAssType src o (text $ show o ++ "type error") g (rHole rr)
    rr  = F.toReft r
    tag = getTag γ
    src = getLocation γ
    g   = reLocal $ renv γ

traceTy :: SpecType -> String 
traceTy (RVar v _)      = parens ("RVar " ++ showpp v)
traceTy (RApp c ts _ _) = parens ("RApp " ++ showpp c ++ unwords (traceTy <$> ts)) 
traceTy (RAllP _ t)     = parens ("RAllP " ++ traceTy t)
traceTy (RAllT _ t _)   = parens ("RAllT " ++ traceTy t)
traceTy (RImpF _ _ t t' _) = parens ("RImpF " ++ parens (traceTy t) ++ parens (traceTy t'))
traceTy (RFun _ _ t t' _) = parens ("RFun " ++ parens (traceTy t) ++ parens (traceTy t'))
traceTy (RAllE _ tx t)  = parens ("RAllE " ++ parens (traceTy tx) ++ parens (traceTy t))
traceTy (REx _ tx t)    = parens ("REx " ++ parens (traceTy tx) ++ parens (traceTy t))
traceTy (RExprArg _)    = "RExprArg"
traceTy (RAppTy t t' _) = parens ("RAppTy " ++ parens (traceTy t) ++ parens (traceTy t'))
traceTy (RHole _)       = "rHole"
traceTy (RRTy _ _ _ t)  = parens ("RRTy " ++ traceTy t)

parens :: String -> String
parens s = "(" ++ s ++ ")"

rHole :: F.Reft -> SpecType
rHole = RHole . uTop


splitsCWithVariance :: CGEnv
                    -> [SpecType]
                    -> [SpecType]
                    -> [Variance]
                    -> CG [FixSubC]
splitsCWithVariance γ t1s t2s variants
  = concatMapM (\(t1, t2, v) -> splitfWithVariance (\s1 s2 -> (splitC (typeclass (getConfig γ)) (SubC γ s1 s2))) t1 t2 v) (zip3 t1s t2s variants)

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
  temp   <- getTemplates
  isHO   <- allowHO   <$> get
  t1'    <- addLhsInv γ <$> refreshVV t1
  return  $ bsplitC' γ t1' t2 temp isHO

addLhsInv :: CGEnv -> SpecType -> SpecType
addLhsInv γ t = addRTyConInv (invs γ) t `strengthen` r
  where
    r         = (mempty :: UReft F.Reft) { ur_reft = F.Reft (F.dummySymbol, p) }
    p         = constraintToLogic rE' (lcs γ)
    rE'       = insertREnv v t (renv γ)
    v         = rTypeValueVar t


bsplitC' :: CGEnv -> SpecType -> SpecType -> F.Templates -> Bool -> [F.SubC Cinfo]
bsplitC' γ t1 t2 tem isHO
 | isHO
 = mkSubC γ' r1'  r2' tag ci
 | F.isFunctionSortedReft r1' && F.isNonTrivial r2'
 = mkSubC γ' (r1' {F.sr_reft = mempty}) r2' tag ci
 | F.isNonTrivial r2'
 = mkSubC γ' r1'  r2' tag ci
 | otherwise
 = []
  where
    γ'  = feBinds $ fenv γ
    r1' = rTypeSortedReft' γ tem t1
    r2' = rTypeSortedReft' γ tem t2
    ci  = \sr -> Ci src (err sr) (cgVar γ)
    tag = getTag γ
    err = \sr -> Just $ fromMaybe (ErrSubType src (text "subtype") Nothing g t1 (replaceTop t2 sr)) (cerr γ)
    src = getLocation γ
    g   = reLocal $ renv γ

mkSubC :: F.IBindEnv -> F.SortedReft -> F.SortedReft -> F.Tag -> (F.SortedReft -> a) -> [F.SubC a]
mkSubC g sr1 sr2 tag ci = concatMap (\sr2' -> F.subC g sr1 sr2' Nothing tag (ci sr2')) (splitSortedReft sr2)

splitSortedReft :: F.SortedReft -> [F.SortedReft]
splitSortedReft (F.RR t (F.Reft (v, r))) = [ F.RR t (F.Reft (v, ra)) | ra <- refaConjuncts r ]

refaConjuncts :: F.Expr -> [F.Expr]
refaConjuncts p = [p' | p' <- F.conjuncts p, not $ F.isTautoPred p']

replaceTop :: SpecType -> F.SortedReft -> SpecType
replaceTop (RApp c ts rs r) r'  = RApp c ts rs $ replaceReft r r'
replaceTop (RVar a r) r'        = RVar a       $ replaceReft r r'
replaceTop (RFun b i t1 t2 r) r' = RFun b i t1 t2 $ replaceReft r r'
replaceTop (RAppTy t1 t2 r) r'  = RAppTy t1 t2 $ replaceReft r r'
replaceTop (RAllT a t r)    r'  = RAllT a t    $ replaceReft r r'
replaceTop t _                  = t

replaceReft :: RReft -> F.SortedReft -> RReft
replaceReft rr (F.RR _ r) = rr {ur_reft = F.Reft (v, F.subst1  p (vr, F.EVar v) )}
  where
    F.Reft (v, _)         = ur_reft rr
    F.Reft (vr,p)         = r

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
  = do γ'  <-  foldM (+=) γ [("rsplitC1", x, ofRSort s) | (x, s) <- s2]
       splitC (typeclass (getConfig γ)) (SubC γ' (F.subst su r1) r2)
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
      Just (_,_,_,_,t)  -> Just $ F.sr_reft $ rTypeSortedReft (emb γ) t
      Nothing         -> Nothing

forallExprReft_ γ (F.EVar f, es)
  = case forallExprReftLookup γ f of
      Just (xs,_,_,_,t) -> let su = F.mkSubst $ safeZip "fExprRefType" xs es in
                       Just $ F.subst su $ F.sr_reft $ rTypeSortedReft (emb γ) t
      Nothing       -> Nothing

forallExprReft_ _ _
  = Nothing

-- forallExprReftLookup :: CGEnv -> F.Symbol -> Int
forallExprReftLookup :: CGEnv
                     -> F.Symbol
                     -> Maybe ([F.Symbol], [RFInfo], [SpecType], [RReft], SpecType)
forallExprReftLookup γ sym = snap <$> F.lookupSEnv sym (syenv γ)
  where
    snap     = mapFifth5 ignoreOblig . (\(_,(x,a,b,c),t)->(x,a,b,c,t)) . bkArrow . thd3 . bkUniv . lookup'
    lookup' z = fromMaybe (panicUnbound γ z) (γ ?= F.symbol z)


--------------------------------------------------------------------------------
getTag :: CGEnv -> F.Tag
--------------------------------------------------------------------------------
getTag γ = maybe Tg.defaultTag (`Tg.getTag` tgEnv γ) (tgKey γ)


--------------------------------------------------------------------------------
-- | Constraint Generation Panic -----------------------------------------------
--------------------------------------------------------------------------------
panicUnbound :: (PPrint x) => CGEnv -> x -> a
panicUnbound γ x = Ex.throw $ (ErrUnbound (getLocation γ) (F.pprint x) :: Error)
