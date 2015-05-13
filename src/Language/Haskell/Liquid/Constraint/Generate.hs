{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}

-- | This module defines the representation of Subtyping and WF Constraints, and
-- the code for syntax-directed constraint generation.

module Language.Haskell.Liquid.Constraint.Generate (

   generateConstraints

  ) where

import CoreUtils     (exprType)

import CoreSyn
import SrcLoc
import Type
import PrelNames
import TypeRep
import Class            (Class, className)
import Var
import Id
import Name
import NameSet
import Text.PrettyPrint.HughesPJ hiding (first)

import Control.Monad.State

import Control.Applicative      ((<$>))

import Data.Monoid              (mconcat, mempty, mappend)
import Data.Maybe               (fromMaybe, catMaybes, fromJust, isJust)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L
import qualified Data.Text           as T
import Data.Bifunctor
import Data.List (foldl')
import qualified Data.Foldable    as F
import qualified Data.Traversable as T

import Text.Printf

import qualified Language.Haskell.Liquid.CTags      as Tg
import Language.Fixpoint.Sort (pruneUnsortedReft)
import Language.Fixpoint.Visitor

import Language.Haskell.Liquid.Fresh

import qualified Language.Fixpoint.Types            as F

import Language.Haskell.Liquid.Dictionaries
import Language.Haskell.Liquid.Variance
import Language.Haskell.Liquid.Types            hiding (binds, Loc, loc, freeTyVars, Def)
import Language.Haskell.Liquid.Strata
import Language.Haskell.Liquid.Bounds
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.Visitors
import Language.Haskell.Liquid.PredType         hiding (freeTyVars)
import Language.Haskell.Liquid.GhcMisc          ( isInternal, collectArguments, tickSrcSpan
                                                , hasBaseTypeVar, showPpr, isDataConId)
import Language.Haskell.Liquid.Misc
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.Literals
import Language.Haskell.Liquid.RefSplit
import Control.DeepSeq

import Language.Haskell.Liquid.Constraint.Types
import Language.Haskell.Liquid.Constraint.Constraint

-----------------------------------------------------------------------
------------- Constraint Generation: Toplevel -------------------------
-----------------------------------------------------------------------

generateConstraints      :: GhcInfo -> CGInfo
generateConstraints info = {-# SCC "ConsGen" #-} execState act $ initCGI cfg info
  where
    act                  = consAct info
    cfg                  = config $ spec info


consAct info
  = do γ     <- initEnv info
       sflag <- scheck <$> get
       tflag <- trustghc <$> get
       let trustBinding x = if tflag
                             then (x `elem` (derVars info) || isInternal x)
                             else False
       foldM_ (consCBTop trustBinding) γ (cbs info)
       hcs <- hsCs  <$> get
       hws <- hsWfs <$> get
       scss <- sCs <$> get
       annot <- annotMap <$> get
       scs <- if sflag then concat <$> mapM splitS (hcs ++ scss)
                       else return []
       let smap = if sflag then solveStrata scs else []
       let hcs' = if sflag then subsS smap hcs else hcs
       fcs <- concat <$> mapM splitC (subsS smap hcs')
       fws <- concat <$> mapM splitW hws
       let annot' = if sflag then (\t -> subsS smap t) <$> annot else annot
       modify $ \st -> st { fixCs = fcs } { fixWfs = fws } {annotMap = annot'}

------------------------------------------------------------------------------------
initEnv :: GhcInfo -> CG CGEnv
------------------------------------------------------------------------------------
initEnv info
  = do let tce   = tcEmbeds sp
       let fVars = impVars info
       let dcs   = filter isConLikeId (snd <$> freeSyms sp)
       defaults <- forM fVars $ \x -> liftM (x,) (trueTy $ varType x)
       dcsty    <- forM dcs   $ \x -> liftM (x,) (trueTy $ varType x)
       (hs,f0)  <- refreshHoles $ grty info                  -- asserted refinements     (for defined vars)
       f0''     <- refreshArgs' =<< grtyTop info             -- default TOP reftype      (for exported vars without spec)
       let f0'   = if notruetypes $ config sp then [] else f0''
       f1       <- refreshArgs' $ defaults                   -- default TOP reftype      (for all vars)
       f1'      <- refreshArgs' $ makedcs dcsty              -- default TOP reftype      (for data cons)
       f2       <- refreshArgs' $ assm info                  -- assumed refinements      (for imported vars)
       f3       <- refreshArgs' $ vals asmSigs sp            -- assumed refinedments     (with `assume`)
       f4       <- refreshArgs' $ makedcs $ vals ctors sp    -- constructor refinements  (for measures)
       sflag    <- scheck <$> get
       let senv  = if sflag then f2 else []
       let tx    = mapFst F.symbol . addRInv ialias . strataUnify senv . predsUnify sp
       let bs    = (tx <$> ) <$> [f0 ++ f0', f1 ++ f1', f2, f3, f4]
       lts      <- lits <$> get
       let tcb   = mapSnd (rTypeSort tce) <$> concat bs
       let γ0    = measEnv sp (head bs) (cbs info) (tcb ++ lts) (bs!!3) hs
       foldM (++=) γ0 [("initEnv", x, y) | (x, y) <- concat $ tail bs]
  where
    sp           = spec info
    ialias       = mkRTyConIAl $ ialiases sp
    vals f       = map (mapSnd val) . f
    makedcs      = map strengthenDataConType

refreshHoles vts = first catMaybes . unzip . map extract <$> mapM refreshHoles' vts
refreshHoles' (x,t)
  | noHoles t = return (Nothing,x,t)
  | otherwise = (Just $ F.symbol x,x,) <$> mapReftM tx t
  where
    tx r | hasHole r = refresh r
         | otherwise = return r
extract (a,b,c) = (a,(b,c))

refreshArgs' = mapM (mapSndM refreshArgs)

strataUnify :: [(Var, SpecType)] -> (Var, SpecType) -> (Var, SpecType)
strataUnify senv (x, t) = (x, maybe t (mappend t) pt)
  where
    pt                  = (fmap (\(U _ _ l) -> U mempty mempty l)) <$> L.lookup x senv


-- | TODO: All this *should* happen inside @Bare@ but appears
--   to happen after certain are signatures are @fresh@-ed,
--   which is why they are here.

-- NV : still some sigs do not get TyConInfo

predsUnify :: GhcSpec -> (Var, RRType RReft) -> (Var, RRType RReft)
predsUnify sp = second (addTyConInfo tce tyi) -- needed to eliminate some @RPropH@

  where
    tce            = tcEmbeds sp
    tyi            = tyconEnv sp

 ---------------------------------------------------------------------------------------
 ---------------------------------------------------------------------------------------
 ---------------------------------------------------------------------------------------

measEnv sp xts cbs lts asms hs
  = CGE { loc   = noSrcSpan
        , renv  = fromListREnv $ second val <$> meas sp
        , syenv = F.fromListSEnv $ freeSyms sp
        , fenv  = initFEnv $ lts ++ (second (rTypeSort tce . val) <$> meas sp)
        , denv  = dicts sp
        , recs  = S.empty
        , invs  = mkRTyConInv    $ invariants sp
        , ial   = mkRTyConIAl    $ ialiases   sp
        , grtys = fromListREnv xts
        , assms = fromListREnv asms
        , emb   = tce
        , tgEnv = Tg.makeTagEnv cbs
        , tgKey = Nothing
        , trec  = Nothing
        , lcb   = M.empty
        , holes = fromListHEnv hs
        , lcs   = mempty
        }
    where
      tce = tcEmbeds sp

assm = assm_grty impVars
grty = assm_grty defVars

assm_grty f info = [ (x, val t) | (x, t) <- sigs, x `S.member` xs ]
  where
    xs           = S.fromList $ f info
    sigs         = tySigs     $ spec info

grtyTop info     = forM topVs $ \v -> (v,) <$> (trueTy $ varType v) -- val $ varSpecType v) | v <- defVars info, isTop v]
  where
    topVs        = filter isTop $ defVars info
    isTop v      = isExportedId v && not (v `S.member` sigVs)
    isExportedId = flip elemNameSet (exports $ spec info) . getName
    sigVs        = S.fromList $ [v | (v,_) <- (tySigs $ spec info)
                                           ++ (asmSigs $ spec info)]


------------------------------------------------------------------------
-- | Helpers: Reading/Extending Environment Bindings -------------------
------------------------------------------------------------------------



getTag :: CGEnv -> F.Tag
getTag γ = maybe Tg.defaultTag (`Tg.getTag` (tgEnv γ)) (tgKey γ)

setLoc :: CGEnv -> SrcSpan -> CGEnv
γ `setLoc` src
  | isGoodSrcSpan src = γ { loc = src }
  | otherwise         = γ

withRecs :: CGEnv -> [Var] -> CGEnv
withRecs γ xs  = γ { recs = foldl' (flip S.insert) (recs γ) xs }

withTRec γ xts = γ' {trec = Just $ M.fromList xts' `M.union` trec'}
  where γ'    = γ `withRecs` (fst <$> xts)
        trec' = fromMaybe M.empty $ trec γ
        xts'  = mapFst F.symbol <$> xts

setBind :: CGEnv -> Tg.TagKey -> CGEnv
setBind γ k
  | Tg.memTagEnv k (tgEnv γ) = γ { tgKey = Just k }
  | otherwise                = γ


isGeneric :: RTyVar -> SpecType -> Bool
isGeneric α t =  all (\(c, α') -> (α'/=α) || isOrd c || isEq c ) (classConstrs t)
  where classConstrs t = [(c, α') | (c, ts) <- tyClasses t
                                  , t'      <- ts
                                  , α'      <- freeTyVars t']
        isOrd          = (ordClassName ==) . className
        isEq           = (eqClassName ==) . className


------------------------------------------------------------
------------------- Constraint Splitting -------------------
------------------------------------------------------------

splitW ::  WfC -> CG [FixWfC]

splitW (WfC γ t@(RFun x t1 t2 _))
  =  do ws   <- bsplitW γ t
        ws'  <- splitW (WfC γ t1)
        γ'   <- (γ, "splitW") += (x, t1)
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
        ws'   <- concat <$> mapM splitW (map (WfC γ') ts)
        ws''  <- concat <$> mapM (rsplitW γ) rs
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
  = errorstar $ "splitW cannot handle: " ++ showpp t

rsplitW _ (RPropP _ _)
  = errorstar "Constrains: rsplitW for RPropP"
rsplitW γ (RProp ss t0)
  = do γ' <- foldM (++=) γ [("rsplitC", x, ofRSort s) | (x, s) <- ss]
       splitW $ WfC γ' t0
rsplitW _ (RHProp _ _)
  = errorstar "TODO: EFFECTS"

bsplitW :: CGEnv -> SpecType -> CG [FixWfC]
bsplitW γ t = pruneRefs <$> get >>= return . bsplitW' γ t

bsplitW' γ t pflag
  | F.isNonTrivial r' = [F.wfC (fe_binds $ fenv γ) r' Nothing ci]
  | otherwise         = []
  where
    r'                = rTypeSortedReft' pflag γ t
    ci                = Ci (loc γ) Nothing

------------------------------------------------------------
splitS  :: SubC -> CG [([Stratum], [Stratum])]
bsplitS :: SpecType -> SpecType -> CG [([Stratum], [Stratum])]
------------------------------------------------------------

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
        γ'       <- (γ, "splitC") += (x2, r2)
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
  = errorstar $ "Predicate in lhs of constrain:" ++ showpp t1 ++ "\n<:\n" ++ showpp t2

splitS (SubC γ (RAllT α1 t1) (RAllT α2 t2))
  |  α1 ==  α2
  = splitS $ SubC γ t1 t2
  | otherwise
  = splitS $ SubC γ t1 t2'
  where t2' = subsTyVar_meet' (α2, RVar α1 mempty) t2

splitS (SubC _ (RApp c1 _ _ _) (RApp c2 _ _ _)) | isClass c1 && c1 == c2
  = return []


splitS (SubC γ t1@(RApp _ _ _ _) t2@(RApp _ _ _ _))
  = do (t1',t2') <- unifyVV t1 t2
       cs    <- bsplitS t1' t2'
       γ'    <- γ `extendEnvWithVV` t1'
       let RApp c t1s r1s _ = t1'
       let RApp _ t2s r2s _ = t2'
       let tyInfo = rtc_info c
       csvar  <-  splitsSWithVariance γ' t1s t2s $ varianceTyArgs tyInfo
       csvar' <- rsplitsSWithVariance γ' r1s r2s $ variancePsArgs tyInfo
       return $ cs ++ csvar ++ csvar'

splitS (SubC _ t1@(RVar a1 _) t2@(RVar a2 _))
  | a1 == a2
  = bsplitS t1 t2

splitS (SubC _ t1 t2)
  = errorstar $ "(Another Broken Test!!!) splitS unexpected: " ++ showpp t1 ++ "\n\n" ++ showpp t2

splitS (SubR _ _ _)
  = return []

splitsSWithVariance γ t1s t2s variants
  = concatMapM (\(t1, t2, v) -> splitfWithVariance (\s1 s2 -> splitS (SubC γ s1 s2)) t1 t2 v) (zip3 t1s t2s variants)

rsplitsSWithVariance γ t1s t2s variants
  = concatMapM (\(t1, t2, v) -> splitfWithVariance (rsplitS γ) t1 t2 v) (zip3 t1s t2s variants)

bsplitS t1 t2
  = return $ [(s1, s2)]
  where [s1, s2]   = getStrata <$> [t1, t2]

rsplitS γ (RProp s1 r1) (RProp s2 r2)
  = splitS (SubC γ (F.subst su r1) r2)
  where su = F.mkSubst [(x, F.EVar y) | ((x,_), (y,_)) <- zip s1 s2]

rsplitS _ _ _
  = errorstar "rspliS Rpoly - RPropP"



splitfWithVariance f t1 t2 Invariant     = liftM2 (++) (f t1 t2) (f t2 t1) -- return []
splitfWithVariance f t1 t2 Bivariant     = liftM2 (++) (f t1 t2) (f t2 t1)
splitfWithVariance f t1 t2 Covariant     = f t1 t2
splitfWithVariance f t1 t2 Contravariant = f t2 t1


------------------------------------------------------------
splitC :: SubC -> CG [FixSubC]
------------------------------------------------------------

splitC (SubC γ (REx x tx t1) (REx x2 _ t2)) | x == x2
  = do γ' <- (γ, "addExBind 0") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ t1 (REx x tx t2))
  = do γ' <- (γ, "addExBind 1") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)

-- existential at the left hand side is treated like forall
splitC (SubC γ (REx x tx t1) t2)
  = do -- let tx' = traceShow ("splitC: " ++ showpp z) tx
       γ' <- (γ, "addExBind 1") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ (RAllE x tx t1) (RAllE x2 _ t2)) | x == x2
  = do γ' <- (γ, "addExBind 0") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ (RAllE x tx t1) t2)
  = do γ' <- (γ, "addExBind 2") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ t1 (RAllE x tx t2))
  = do γ' <- (γ, "addExBind 2") += (x, forallExprRefType γ tx)
       splitC (SubC γ' t1 t2)

splitC (SubC γ (RRTy env _ OCons t1) t2)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("splitS", x,t)) γ xts
       c1 <- splitC (SubC γ' t1' t2')
       c2 <- splitC (SubC γ  t1  t2 )
       return $ c1 ++ c2
  where
    (xts, t1', t2') = envToSub env

splitC (SubC γ (RRTy e r o t1) t2)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("splitS", x,t)) γ e
       c1 <- splitC (SubR γ' o  r )
       c2 <- splitC (SubC γ t1 t2)
       return $ c1 ++ c2

splitC (SubC γ t1@(RFun x1 r1 r1' _) t2@(RFun x2 r2 r2' _))
  =  do cs       <- bsplitC γ t1 t2
        cs'      <- splitC  (SubC γ r2 r1)
        γ'       <- (γ, "splitC") += (x2, r2)
        let r1x2' = r1' `F.subst1` (x1, F.EVar x2)
        cs''     <- splitC  (SubC γ' r1x2' r2')
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

splitC (SubC _ t1@(RAllP _ _) t2)
  = errorstar $ "Predicate in lhs of constraint:" ++ showpp t1 ++ "\n<:\n" ++ showpp t2

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
       let tyInfo = rtc_info c
       csvar  <-  splitsCWithVariance γ' t1s t2s $ varianceTyArgs tyInfo
       csvar' <- rsplitsCWithVariance γ' r1s r2s $ variancePsArgs tyInfo
       return $ cs ++ csvar ++ csvar'

splitC (SubC γ t1@(RVar a1 _) t2@(RVar a2 _))
  | a1 == a2
  = bsplitC γ t1 t2

splitC (SubC _ t1 t2)
  = errorstar $ "(Another Broken Test!!!) splitc unexpected: " ++ showpp t1 ++ "\n\n" ++ showpp t2

splitC (SubR γ o r)
  = do fg     <- pruneRefs <$> get
       let r1' = if fg then pruneUnsortedReft γ'' r1 else r1
       return $ F.subC γ' F.PTrue r1' r2 Nothing tag ci
  where
    γ'' = fe_env $ fenv γ
    γ'  = fe_binds $ fenv γ
    r1  = F.RR s $ F.toReft r
    r2  = F.RR s $ F.Reft (vv, F.Refa $ F.PBexp $ F.EVar vv)
    vv  = "vvRec"
    s   = F.FApp F.boolFTyCon []
    ci  = Ci src err
    err = Just $ ErrAssType src o (text $ show o ++ "type error") r
    tag = getTag γ
    src = loc γ


splitsCWithVariance γ t1s t2s variants
  = concatMapM (\(t1, t2, v) -> splitfWithVariance (\s1 s2 -> (splitC (SubC γ s1 s2))) t1 t2 v) (zip3 t1s t2s variants)

rsplitsCWithVariance γ t1s t2s variants
  = concatMapM (\(t1, t2, v) -> splitfWithVariance (rsplitC γ) t1 t2 v) (zip3 t1s t2s variants)



bsplitC γ t1 t2
  = do checkStratum γ t1 t2
       pflag <- pruneRefs <$> get
       γ' <- γ ++= ("bsplitC", v, t1)
       let r = (mempty :: UReft F.Reft){ur_reft = F.Reft (F.dummySymbol,  F.Refa $ constraintToLogic γ' (lcs γ'))}
       let t1' = addRTyConInv (invs γ')  t1 `strengthen` r
       return $ bsplitC' γ' t1' t2 pflag
  where
    F.Reft(v, _) = ur_reft (fromMaybe mempty (stripRTypeBase t1))

checkStratum γ t1 t2
  | s1 <:= s2 = return ()
  | otherwise = addWarning wrn
  where
    [s1, s2]  = getStrata <$> [t1, t2]
    wrn       =  ErrOther (loc γ) (text $ "Stratum Error : " ++ show s1 ++ " > " ++ show s2)

bsplitC' γ t1 t2 pflag
  | F.isFunctionSortedReft r1' && F.isNonTrivial r2'
  = F.subC γ' grd (r1' {F.sr_reft = mempty}) r2' Nothing tag ci
  | F.isNonTrivial r2'
  = F.subC γ' grd r1'  r2' Nothing tag ci
  | otherwise
  = []
  where
    γ'     = fe_binds $ fenv γ
    r1'    = rTypeSortedReft' pflag γ t1
    r2'    = rTypeSortedReft' pflag γ t2
    ci     = Ci src err
    tag    = getTag γ
    err    = Just $ ErrSubType src (text "subtype") g t1 t2
    src    = loc γ
    REnv g = renv γ
    grd    = F.PTrue



unifyVV t1@(RApp _ _ _ _) t2@(RApp _ _ _ _)
  = do vv     <- (F.vv . Just) <$> fresh
       return  $ (shiftVV t1 vv,  (shiftVV t2 vv) ) -- {rt_pargs = r2s'})

unifyVV _ _
  = errorstar $ "Constraint.Generate.unifyVV called on invalid inputs"

rsplitC _ (RPropP _ _) (RPropP _ _)
  = errorstar "RefTypes.rsplitC on RPropP"

rsplitC γ (RProp s1 r1) (RProp s2 r2)
  = do γ'  <-  foldM (++=) γ [("rsplitC1", x, ofRSort s) | (x, s) <- s2]
       splitC (SubC γ' (F.subst su r1) r2)
  where su = F.mkSubst [(x, F.EVar y) | ((x,_), (y,_)) <- zip s1 s2]

rsplitC _ _ _
  = errorstar "rsplit Rpoly - RPropP"


type CG = State CGInfo

initCGI cfg info = CGInfo {
    hsCs       = []
  , sCs        = []
  , hsWfs      = []
  , fixCs      = []
  , isBind     = []
  , fixWfs     = []
  , freshIndex = 0
  , binds      = F.emptyBindEnv
  , annotMap   = AI M.empty
  , tyConInfo  = tyi
  , tyConEmbed = tce
  , kuts       = F.ksEmpty
  , lits       = coreBindLits tce info
  , termExprs  = M.fromList $ texprs spc
  , specDecr   = decr spc
  , specLVars  = lvars spc
  , specLazy   = lazy spc
  , tcheck     = not $ notermination cfg
  , scheck     = strata cfg
  , trustghc   = trustinternals cfg
  , pruneRefs  = not $ noPrune cfg
  , logErrors  = []
  , kvProf     = emptyKVProf
  , recCount   = 0
  }
  where
    tce        = tcEmbeds spc
    spc        = spec info
    tyi        = tyconEnv spc -- EFFECTS HEREHEREHERE makeTyConInfo (tconsP spc)

coreBindLits tce info
  = sortNub      $ [ (val x, so) | (_, Just (F.ELit x so)) <- lconsts ]
                ++ [(F.symbol x, F.strSort) | (_, Just (F.ESym x)) <- lconsts ]
                ++ [ (dconToSym dc, dconToSort dc) | dc <- dcons ]
  where
    lconsts      = literalConst tce <$> literals (cbs info)
    dcons        = filter isDCon $ impVars info -- ++ (snd <$> freeSyms (spec info))
    dconToSort   = typeSort tce . expandTypeSynonyms . varType
    dconToSym    = dataConSymbol . idDataCon
    isDCon x     = isDataConId x && not (hasBaseTypeVar x)

extendEnvWithVV γ t
  | F.isNontrivialVV vv
  = (γ, "extVV") += (vv, t)
  | otherwise
  = return γ
  where vv = rTypeValueVar t

{- see tests/pos/polyfun for why you need everything in fixenv -}
addCGEnv :: (SpecType -> SpecType) -> CGEnv -> (String, F.Symbol, SpecType) -> CG CGEnv
addCGEnv tx γ (msg, x, REx y tyy tyx)
  = do y' <- fresh
       γ' <- addCGEnv tx γ (msg, y', tyy)
       addCGEnv tx γ' (msg, x, tyx `F.subst1` (y, F.EVar y'))

addCGEnv tx γ (msg, x, RAllE yy tyy tyx)
  = addCGEnv tx γ (msg, x, t)
  where
    xs    = grapBindsWithType tyy γ
    t     = foldl (\t1 t2 -> t1 `F.meet` t2) ttrue [ tyx' `F.subst1` (yy, F.EVar x) | x <- xs]

    (tyx', ttrue) = splitXRelatedRefs yy tyx

addCGEnv tx γ (_, x, t')
  = do idx   <- fresh
       let t  = tx $ normalize {-x-} idx t'
       let γ' = γ { renv = insertREnv x t (renv γ) }
       pflag <- pruneRefs <$> get
       is    <- if isBase t
                  then liftM2 (++) (liftM single $ addBind x $ rTypeSortedReft' pflag γ' t) (addClassBind t)
                  else return [] -- addClassBind t
       return $ γ' { fenv = insertsFEnv (fenv γ) is }

(++=) :: CGEnv -> (String, F.Symbol, SpecType) -> CG CGEnv
(++=) γ = addCGEnv (addRTyConInv (M.unionWith mappend (invs γ) (ial γ))) γ

addSEnv :: CGEnv -> (String, F.Symbol, SpecType) -> CG CGEnv
addSEnv γ = addCGEnv (addRTyConInv (invs γ)) γ

rTypeSortedReft' pflag γ
  | pflag
  = pruneUnsortedReft (fe_env $ fenv γ) . f
  | otherwise
  = f
  where
    f = rTypeSortedReft (emb γ)

(+++=) :: (CGEnv, String) -> (F.Symbol, CoreExpr, SpecType) -> CG CGEnv

(γ, _) +++= (x, e, t) = (γ{lcb = M.insert x e (lcb γ)}, "+++=") += (x, t)

(+=) :: (CGEnv, String) -> (F.Symbol, SpecType) -> CG CGEnv
(γ, msg) += (x, r)
  | x == F.dummySymbol
  = return γ
  | x `memberREnv` (renv γ)
  = err
  | otherwise
  =  γ ++= (msg, x, r)
  where err = errorstar $ msg ++ " Duplicate binding for "
                              ++ F.symbolString x
                              ++ "\n New: " ++ showpp r
                              ++ "\n Old: " ++ showpp (x `lookupREnv` (renv γ))

γ -= x =  γ {renv = deleteREnv x (renv γ), lcb  = M.delete x (lcb γ)}

(??=) :: CGEnv -> F.Symbol -> CG SpecType
γ ??= x
  = case M.lookup x (lcb γ) of
    Just e  -> consE (γ-=x) e
    Nothing -> refreshTy $ γ ?= x

(?=) ::  CGEnv -> F.Symbol -> SpecType
γ ?= x = fromMaybe err $ lookupREnv x (renv γ)
         where err = errorstar $ "EnvLookup: unknown "
                               ++ showpp x
                               ++ " in renv "
                               ++ showpp (renv γ)

normalize idx
  = normalizeVV idx
  . normalizePds

normalizeVV idx t@(RApp _ _ _ _)
  | not (F.isNontrivialVV (rTypeValueVar t))
  = shiftVV t (F.vv $ Just idx)

normalizeVV _ t
  = t


addBind :: F.Symbol -> F.SortedReft -> CG ((F.Symbol, F.Sort), F.BindId)
addBind x r
  = do st          <- get
       let (i, bs') = F.insertBindEnv x r (binds st)
       put          $ st { binds = bs' }
       return ((x, F.sr_sort r), i) -- traceShow ("addBind: " ++ showpp x) i

addClassBind :: SpecType -> CG [((F.Symbol, F.Sort), F.BindId)]
addClassBind = mapM (uncurry addBind) . classBinds

-- RJ: What is this `isBind` business?
pushConsBind act
  = do modify $ \s -> s { isBind = False : isBind s }
       z <- act
       modify $ \s -> s { isBind = tail (isBind s) }
       return z

addC :: SubC -> String -> CG ()
addC !c@(SubC γ t1 t2) _msg
  = do -- trace ("addC at " ++ show (loc γ) ++ _msg++ showpp t1 ++ "\n <: \n" ++ showpp t2 ) $
       modify $ \s -> s { hsCs  = c : (hsCs s) }
       bflag <- headDefault True . isBind <$> get
       sflag <- scheck                 <$> get
       if bflag && sflag
         then modify $ \s -> s {sCs = (SubC γ t2 t1) : (sCs s) }
         else return ()
  where
    headDefault a []    = a
    headDefault _ (x:_) = x


addC !c _msg
  = modify $ \s -> s { hsCs  = c : (hsCs s) }

addPost γ (RRTy e r OInv t)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("addPost", x,t)) γ e
       addC (SubR γ' OInv r) "precondition" >> return t

addPost γ (RRTy e r OTerm t)
  = do γ' <- foldM (\γ (x, t) -> γ ++= ("addPost", x,t)) γ e
       addC (SubR γ' OTerm r) "precondition" >> return t

addPost _ (RRTy _ _ OCons t)
  = return t

addPost _ t
  = return t

addW   :: WfC -> CG ()
addW !w = modify $ \s -> s { hsWfs = w : (hsWfs s) }

addWarning   :: TError SpecType -> CG ()
addWarning w = modify $ \s -> s { logErrors = w : (logErrors s) }

-- | Used for annotation binders (i.e. at binder sites)

addIdA            :: Var -> Annot SpecType -> CG ()
addIdA !x !t      = modify $ \s -> s { annotMap = upd $ annotMap s }
  where
    loc           = getSrcSpan x
    upd m@(AI _)  = if boundRecVar loc m then m else addA loc (Just x) t m

boundRecVar l (AI m) = not $ null [t | (_, AnnRDf t) <- M.lookupDefault [] l m]


-- | Used for annotating reads (i.e. at Var x sites)

addLocA :: Maybe Var -> SrcSpan -> Annot SpecType -> CG ()
addLocA !xo !l !t
  = modify $ \s -> s { annotMap = addA l xo t $ annotMap s }

-- | Used to update annotations for a location, due to (ghost) predicate applications

updateLocA (_:_)  (Just l) t = addLocA Nothing l (AnnUse t)
updateLocA _      _        _ = return ()

addA !l xo@(Just _) !t (AI m)
  | isGoodSrcSpan l
  = AI $ inserts l (T.pack . showPpr <$> xo, t) m
addA !l xo@Nothing  !t (AI m)
  | l `M.member` m                  -- only spans known to be variables
  = AI $ inserts l (T.pack . showPpr <$> xo, t) m
addA _ _ _ !a
  = a

-------------------------------------------------------------------
------------------------ Generation: Freshness --------------------
-------------------------------------------------------------------

-- | Right now, we generate NO new pvars. Rather than clutter code
--   with `uRType` calls, put it in one place where the above
--   invariant is /obviously/ enforced.
--   Constraint generation should ONLY use @freshTy_type@ and @freshTy_expr@

freshTy_type        :: KVKind -> CoreExpr -> Type -> CG SpecType
freshTy_type k _ τ  = freshTy_reftype k $ ofType τ

freshTy_expr        :: KVKind -> CoreExpr -> Type -> CG SpecType
freshTy_expr k e _  = freshTy_reftype k $ exprRefType e

freshTy_reftype     :: KVKind -> SpecType -> CG SpecType
-- freshTy_reftype k t = do t <- refresh =<< fixTy t
--                          addKVars k t
--                          return t

freshTy_reftype k t = (fixTy t >>= refresh) =>> addKVars k

-- | Used to generate "cut" kvars for fixpoint. Typically, KVars for recursive
--   definitions, and also to update the KVar profile.

addKVars        :: KVKind -> SpecType -> CG ()
addKVars !k !t  = do when (True)    $ modify $ \s -> s { kvProf = updKVProf k kvars (kvProf s) }
                     when (isKut k) $ modify $ \s -> s { kuts   = F.ksUnion kvars   (kuts s)   }
  where
     kvars      = sortNub $ specTypeKVars t

isKut          :: KVKind -> Bool
isKut RecBindE = True
isKut _        = False

specTypeKVars :: SpecType -> [F.KVar]
specTypeKVars = foldReft ((++) . (kvars . ur_reft)) []

trueTy  :: Type -> CG SpecType
trueTy = ofType' >=> true

ofType' :: Type -> CG SpecType
ofType' = fixTy . ofType

fixTy :: SpecType -> CG SpecType
fixTy t = do tyi   <- tyConInfo  <$> get
             tce   <- tyConEmbed <$> get
             return $ addTyConInfo tce tyi t

refreshArgsTop :: (Var, SpecType) -> CG SpecType
refreshArgsTop (x, t)
  = do (t', su) <- refreshArgsSub t
       modify $ \s -> s {termExprs = M.adjust (F.subst su <$>) x $ termExprs s}
       return t'

refreshArgs :: SpecType -> CG SpecType
refreshArgs t
  = fst <$> refreshArgsSub t


-- NV TODO: this does not refreshes args if they are wrapped in an RRTy
refreshArgsSub :: SpecType -> CG (SpecType, F.Subst)
refreshArgsSub t
  = do ts     <- mapM refreshArgs ts_u
       xs'    <- mapM (\_ -> fresh) xs
       let sus = F.mkSubst <$> (L.inits $ zip xs (F.EVar <$> xs'))
       let su  = last sus
       let ts' = zipWith F.subst sus ts
       let t'  = fromRTypeRep $ trep {ty_binds = xs', ty_args = ts', ty_res = F.subst su tbd}
       return (t', su)
    where
       trep    = toRTypeRep t
       xs      = ty_binds trep
       ts_u    = ty_args  trep
       tbd     = ty_res   trep

instance Freshable CG Integer where
  fresh = do s <- get
             let n = freshIndex s
             put $ s { freshIndex = n + 1 }
             return n


-------------------------------------------------------------------------------
----------------------- TERMINATION TYPE --------------------------------------
-------------------------------------------------------------------------------

makeDecrIndex :: (Var, Template SpecType)-> CG [Int]
makeDecrIndex (x, Assumed t)
  = do dindex <- makeDecrIndexTy x t
       case dindex of
         Left _  -> return []
         Right i -> return i
makeDecrIndex (x, Asserted t)
  = do dindex <- makeDecrIndexTy x t
       case dindex of
         Left msg -> addWarning msg >> return []
         Right i  -> return i
makeDecrIndex _ = return []

makeDecrIndexTy x t
  = do spDecr <- specDecr <$> get
       hint   <- checkHint' (L.lookup x $ spDecr)
       case dindex of
         Nothing -> return $ Left msg -- addWarning msg >> return []
         Just i  -> return $ Right $ fromMaybe [i] hint
    where
       ts         = ty_args trep
       checkHint' = checkHint x ts (isDecreasing cenv)
       dindex     = L.findIndex (isDecreasing cenv) ts
       msg        = ErrTermin [x] (getSrcSpan x) (text "No decreasing parameter")
       cenv       = makeNumEnv ts 
       trep       = toRTypeRep $ unOCons t


recType ((_, []), (_, [], t))
  = t

recType ((vs, indexc), (_, index, t))
  = makeRecType t v dxt index
  where v    = (vs !!)  <$> indexc
        dxt  = (xts !!) <$> index
        xts  = zip (ty_binds trep) (ty_args trep)
        trep = toRTypeRep $ unOCons t

checkIndex (x, vs, t, index)
  = do mapM_ (safeLogIndex msg' vs) index
       mapM  (safeLogIndex msg  ts) index
    where
       loc   = getSrcSpan x
       ts    = ty_args $ toRTypeRep $ unOCons $ unTemplate t
       msg'  = ErrTermin [x] loc (text $ "No decreasing " ++ show index ++ "-th argument on " ++ (showPpr x) ++ " with " ++ (showPpr vs))
       msg   = ErrTermin [x] loc (text "No decreasing parameter")

makeRecType t vs dxs is
  = mergecondition t $ fromRTypeRep $ trep {ty_binds = xs', ty_args = ts'}
  where
    (xs', ts') = unzip $ replaceN (last is) (makeDecrType vdxs) xts
    vdxs       = zip vs dxs
    xts        = zip (ty_binds trep) (ty_args trep)
    trep       = toRTypeRep $ unOCons t

unOCons (RAllT v t)        = RAllT v $ unOCons t
unOCons (RAllP p t)        = RAllP p $ unOCons t
unOCons (RFun x tx t r)    = RFun x (unOCons tx) (unOCons t) r
unOCons (RRTy _ _ OCons t) = unOCons t
unOCons t                  = t


mergecondition (RAllT _ t1) (RAllT v t2)
  = RAllT v $ mergecondition t1 t2
mergecondition (RAllP _ t1) (RAllP p t2)
  = RAllP p $ mergecondition t1 t2
mergecondition (RRTy xts r OCons t1) t2
  = RRTy xts r OCons (mergecondition t1 t2)
mergecondition (RFun _ t11 t12 _) (RFun x2 t21 t22 r2)
  = RFun x2 (mergecondition t11 t21) (mergecondition t12 t22) r2
mergecondition _ t
  = t

safeLogIndex err ls n
  | n >= length ls = addWarning err >> return Nothing
  | otherwise      = return $ Just $ ls !! n

checkHint _ _ _ Nothing
  = return Nothing

checkHint x _ _ (Just ns) | L.sort ns /= ns
  = addWarning (ErrTermin [x] loc (text "The hints should be increasing")) >> return Nothing
  where loc = getSrcSpan x

checkHint x ts f (Just ns)
  = (mapM (checkValidHint x ts f) ns) >>= (return . Just . catMaybes)

checkValidHint x ts f n
  | n < 0 || n >= length ts = addWarning err >> return Nothing
  | f (ts L.!! n)           = return $ Just n
  | otherwise               = addWarning err >> return Nothing
  where err = ErrTermin [x] loc (text $ "Invalid Hint " ++ show (n+1) ++ " for " ++ (showPpr x) ++  "\nin\n" ++ show (ts))
        loc = getSrcSpan x

-------------------------------------------------------------------
-------------------- Generation: Corebind -------------------------
-------------------------------------------------------------------
consCBTop :: (Var -> Bool) -> CGEnv -> CoreBind -> CG CGEnv
consCBLet :: CGEnv -> CoreBind -> CG CGEnv
-------------------------------------------------------------------

consCBLet γ cb
  = do oldtcheck <- tcheck <$> get
       strict    <- specLazy <$> get
       let tflag  = oldtcheck
       let isStr  = tcond cb strict
       modify $ \s -> s{tcheck = tflag && isStr}
       γ' <- consCB (tflag && isStr) isStr γ cb
       modify $ \s -> s{tcheck = oldtcheck}
       return γ'

consCBTop trustBinding γ cb | all trustBinding xs
  = do ts <- mapM trueTy (varType <$> xs)
       foldM (\γ xt -> (γ, "derived") += xt) γ (zip xs' ts)
  where xs             = bindersOf cb
        xs'            = F.symbol <$> xs

consCBTop _ γ cb
  = do oldtcheck <- tcheck <$> get
       strict    <- specLazy <$> get
       let tflag  = oldtcheck
       let isStr  = tcond cb strict
       modify $ \s -> s{tcheck = tflag && isStr}
       γ' <- consCB (tflag && isStr) isStr γ cb
       modify $ \s -> s{tcheck = oldtcheck}
       return γ'

tcond cb strict
  = not $ any (\x -> S.member x strict || isInternal x) (binds cb)
  where binds (NonRec x _) = [x]
        binds (Rec xes)    = fst $ unzip xes

-------------------------------------------------------------------
consCB :: Bool -> Bool -> CGEnv -> CoreBind -> CG CGEnv
-------------------------------------------------------------------

consCBSizedTys γ xes
  = do xets''    <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       sflag     <- scheck <$> get
       let cmakeFinType = if sflag then makeFinType else id
       let cmakeFinTy   = if sflag then makeFinTy   else snd
       let xets = mapThd3 (fmap cmakeFinType) <$> xets''
       ts'      <- mapM (T.mapM refreshArgs) $ (thd3 <$> xets)
       let vs    = zipWith collectArgs ts' es
       is       <- mapM makeDecrIndex (zip xs ts') >>= checkSameLens
       let ts = cmakeFinTy  <$> zip is ts'
       let xeets = (\vis -> [(vis, x) | x <- zip3 xs is $ map unTemplate ts]) <$> (zip vs is)
       (L.transpose <$> mapM checkIndex (zip4 xs vs ts is)) >>= checkEqTypes
       let rts   = (recType <$>) <$> xeets
       let xts   = zip xs ts
       γ'       <- foldM extender γ xts
       let γs    = [γ' `withTRec` (zip xs rts') | rts' <- rts]
       let xets' = zip3 xs es ts
       mapM_ (uncurry $ consBind True) (zip γs xets')
       return γ'
  where
       (xs, es) = unzip xes
       collectArgs    = collectArguments . length . ty_binds . toRTypeRep . unOCons . unTemplate
       checkEqTypes :: [[Maybe SpecType]] -> CG [[SpecType]]
       checkEqTypes x = mapM (checkAll err1 toRSort) (catMaybes <$> x)
       checkSameLens  = checkAll err2 length
       err1           = ErrTermin xs loc $ text "The decreasing parameters should be of same type"
       err2           = ErrTermin xs loc $ text "All Recursive functions should have the same number of decreasing parameters"
       loc            = getSrcSpan (head xs)

       checkAll _   _ []            = return []
       checkAll err f (x:xs)
         | all (==(f x)) (f <$> xs) = return (x:xs)
         | otherwise                = addWarning err >> return []

consCBWithExprs γ xes
  = do xets'     <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       texprs <- termExprs <$> get
       let xtes = catMaybes $ (`lookup` texprs) <$> xs
       sflag     <- scheck <$> get
       let cmakeFinType = if sflag then makeFinType else id
       let xets  = mapThd3 (fmap cmakeFinType) <$> xets'
       let ts    = safeFromAsserted err . thd3 <$> xets
       ts'      <- mapM refreshArgs ts
       let xts   = zip xs (Asserted <$> ts')
       γ'       <- foldM extender γ xts
       let γs    = makeTermEnvs γ' xtes xes ts ts'
       let xets' = zip3 xs es (Asserted <$> ts')
       mapM_ (uncurry $ consBind True) (zip γs xets')
       return γ'
  where (xs, es) = unzip xes
        lookup k m | Just x <- M.lookup k m = Just (k, x)
                   | otherwise              = Nothing
        err      = "Constant: consCBWithExprs"

makeFinTy (ns, t) = fmap go t
  where
    go t = fromRTypeRep $ trep {ty_args = args'}
      where
        trep = toRTypeRep t
        args' = mapNs ns makeFinType $ ty_args trep


makeTermEnvs γ xtes xes ts ts' = withTRec γ . zip xs <$> rts
  where
    vs   = zipWith collectArgs ts es
    ys   = (fst4 . bkArrowDeep) <$> ts
    ys'  = (fst4 . bkArrowDeep) <$> ts'
    sus' = zipWith mkSub ys ys'
    sus  = zipWith mkSub ys ((F.symbol <$>) <$> vs)
    ess  = (\x -> (safeFromJust (err x) $ (x `L.lookup` xtes))) <$> xs
    tes  = zipWith (\su es -> F.subst su <$> es)  sus ess
    tes' = zipWith (\su es -> F.subst su <$> es)  sus' ess
    rss  = zipWith makeLexRefa tes' <$> (repeat <$> tes)
    rts  = zipWith addTermCond ts' <$> rss
    (xs, es)     = unzip xes
    mkSub ys ys' = F.mkSubst [(x, F.EVar y) | (x, y) <- zip ys ys']
    collectArgs  = collectArguments . length . ty_binds . toRTypeRep
    err x        = "Constant: makeTermEnvs: no terminating expression for " ++ showPpr x

consCB tflag _ γ (Rec xes) | tflag
  = do texprs <- termExprs <$> get
       modify $ \i -> i { recCount = recCount i + length xes }
       let xxes = catMaybes $ (`lookup` texprs) <$> xs
       if null xxes
         then consCBSizedTys γ xes
         else check xxes <$> consCBWithExprs γ xes
  where xs = fst $ unzip xes
        check ys r | length ys == length xs = r
                   | otherwise              = errorstar err
        err = printf "%s: Termination expressions should be provided for ALL mutual recursive functions" loc
        loc = showPpr $ getSrcSpan (head xs)
        lookup k m | Just x <- M.lookup k m = Just (k, x)
                   | otherwise              = Nothing

consCB _ str γ (Rec xes) | not str
  = do xets'   <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       sflag     <- scheck <$> get
       let cmakeDivType = if sflag then makeDivType else id
       let xets = mapThd3 (fmap cmakeDivType) <$> xets'
       modify $ \i -> i { recCount = recCount i + length xes }
       let xts = [(x, to) | (x, _, to) <- xets]
       γ'     <- foldM extender (γ `withRecs` (fst <$> xts)) xts
       mapM_ (consBind True γ') xets
       return γ'

consCB _ _ γ (Rec xes)
  = do xets   <- forM xes $ \(x, e) -> liftM (x, e,) (varTemplate γ (x, Just e))
       modify $ \i -> i { recCount = recCount i + length xes }
       let xts = [(x, to) | (x, _, to) <- xets]
       γ'     <- foldM extender (γ `withRecs` (fst <$> xts)) xts
       mapM_ (consBind True γ') xets
       return γ'

-- | NV: Dictionaries are not checked, because
-- | class methods' preconditions are not satisfied
consCB _ _ γ (NonRec x _) | isDictionary x
  = do t  <- trueTy (varType x)
       extender γ (x, Assumed t)
  where
    isDictionary = isJust . dlookup (denv γ)


consCB _ _ γ (NonRec x (App (Var w) (Type τ))) | isDictionary w
  = do t      <- trueTy τ
       addW    $ WfC γ t
       let xts = dmap (f t) $ safeFromJust (show w ++ "Not a dictionary"  ) $ dlookup (denv γ) w
       let  γ' = γ{denv = dinsert (denv γ) x xts }
       t      <- trueTy (varType x)
       extender γ' (x, Assumed t)
  where f t' (RAllT α te) = subsTyVar_meet' (α, t') te
        f _ _ = error "consCB on Dictionary: this should not happen"
        isDictionary = isJust . dlookup (denv γ)



consCB _ _ γ (NonRec x e)
  = do to  <- varTemplate γ (x, Nothing)
       to' <- consBind False γ (x, e, to) >>= (addPostTemplate γ)
       extender γ (x, to')

consBind isRec γ (x, e, Asserted spect)
  = do let γ'         = (γ `setLoc` getSrcSpan x) `setBind` x
           (_,πs,_,_) = bkUniv spect
       γπ    <- foldM addPToEnv γ' πs
       cconsE γπ e spect
       when (F.symbol x `elemHEnv` holes γ) $
         -- have to add the wf constraint here for HOLEs so we have the proper env
         addW $ WfC γπ $ fmap killSubst spect
       addIdA x (defAnn isRec spect)
       return $ Asserted spect -- Nothing

consBind isRec γ (x, e, Assumed spect)
  = do let γ' = (γ `setLoc` getSrcSpan x) `setBind` x
       γπ    <- foldM addPToEnv γ' πs
       cconsE γπ e =<< true spect
       addIdA x (defAnn isRec spect)
       return $ Asserted spect -- Nothing
  where πs   = ty_preds $ toRTypeRep spect

consBind isRec γ (x, e, Unknown)
  = do t     <- consE (γ `setBind` x) e
       addIdA x (defAnn isRec t)
       return $ Asserted t

noHoles = and . foldReft (\r bs -> not (hasHole r) : bs) []

killSubst :: RReft -> RReft
killSubst = fmap killSubstReft

killSubstReft :: F.Reft -> F.Reft
killSubstReft = trans kv () ()
  where
    kv    = defaultVisitor { txPred = ks }
    ks _ (F.PKVar k _) = F.PKVar k mempty
    ks _ p             = p

    -- tx (F.Reft (s, rs)) = F.Reft (s, map f rs)
    -- f (F.RKvar k _)     = F.RKvar k mempty
    -- f (F.RConc p)       = F.RConc p

defAnn True  = AnnRDf
defAnn False = AnnDef

addPToEnv γ π
  = do γπ <- γ ++= ("addSpec1", pname π, pvarRType π)
       foldM (++=) γπ [("addSpec2", x, ofRSort t) | (t, x, _) <- pargs π]

extender γ (x, Asserted t) = γ ++= ("extender", F.symbol x, t)
extender γ (x, Assumed t)  = γ ++= ("extender", F.symbol x, t)
extender γ _               = return γ

addBinders γ0 x' cbs   = foldM (++=) (γ0 -= x') [("addBinders", x, t) | (x, t) <- cbs]

data Template a = Asserted a | Assumed a | Unknown deriving (Functor, F.Foldable, T.Traversable)

deriving instance (Show a) => (Show (Template a))

unTemplate (Asserted t) = t
unTemplate (Assumed t) = t
unTemplate _ = errorstar "Constraint.Generate.unTemplate called on `Unknown`"

addPostTemplate γ (Asserted t) = Asserted <$> addPost γ t
addPostTemplate γ (Assumed  t) = Assumed  <$> addPost γ t
addPostTemplate _ Unknown      = return Unknown

safeFromAsserted _ (Asserted t) = t
safeFromAsserted msg _ = errorstar $ "safeFromAsserted:" ++ msg

-- | @varTemplate@ is only called with a `Just e` argument when the `e`
-- corresponds to the body of a @Rec@ binder.
varTemplate :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Template SpecType)
varTemplate γ (x, eo)
  = case (eo, lookupREnv (F.symbol x) (grtys γ), lookupREnv (F.symbol x) (assms γ)) of
      (_, Just t, _) -> Asserted <$> refreshArgsTop (x, t)
      (_, _, Just t) -> Assumed  <$> refreshArgsTop (x, t)
      (Just e, _, _) -> do t  <- freshTy_expr RecBindE e (exprType e)
                           addW (WfC γ t)
                           Asserted <$> refreshArgsTop (x, t)
      (_,      _, _) -> return Unknown

-------------------------------------------------------------------
-------------------- Generation: Expression -----------------------
-------------------------------------------------------------------

----------------------- Type Checking -----------------------------
cconsE :: CGEnv -> Expr Var -> SpecType -> CG ()
-------------------------------------------------------------------
cconsE γ e@(Let b@(NonRec x _) ee) t
  = do sp <- specLVars <$> get
       if (x `S.member` sp) || isDefLazyVar x
        then cconsLazyLet γ e t
        else do γ'  <- consCBLet γ b
                cconsE γ' ee t
  where
       isDefLazyVar = L.isPrefixOf "fail" . showPpr

cconsE γ e (RAllP p t)
  = cconsE γ' e t''
  where
    t'         = replacePredsWithRefs su <$> t
    su         = (uPVar p, pVartoRConc p)
    (css, t'') = splitConstraints t'
    γ'         = foldl (flip addConstraints) γ css

cconsE γ (Let b e) t
  = do γ'  <- consCBLet γ b
       cconsE γ' e t

cconsE γ (Case e x _ cases) t
  = do γ'  <- consCBLet γ (NonRec x e)
       forM_ cases $ cconsCase γ' x t nonDefAlts
    where
       nonDefAlts = [a | (a, _, _) <- cases, a /= DEFAULT]

cconsE γ (Lam α e) (RAllT α' t) | isTyVar α
  = cconsE γ e $ subsTyVar_meet' (α', rVar α) t

cconsE γ (Lam x e) (RFun y ty t _)
  | not (isTyVar x)
  = do γ' <- (γ, "cconsE") += (F.symbol x, ty)
       cconsE γ' e (t `F.subst1` (y, F.EVar $ F.symbol x))
       addIdA x (AnnDef ty)

cconsE γ (Tick tt e) t
  = cconsE (γ `setLoc` tickSrcSpan tt) e t

cconsE γ e@(Cast e' _) t
  = do t' <- castTy γ (exprType e) e'
       addC (SubC γ t' t) ("cconsE Cast" ++ showPpr e)

cconsE γ e t
  = do te  <- consE γ e
       te' <- instantiatePreds γ e te >>= addPost γ
       addC (SubC γ te' t) ("cconsE" ++ showPpr e)


splitConstraints (RRTy cs _ OCons t)
  = let (css, t') = splitConstraints t in (cs:css, t')
splitConstraints (RFun x tx@(RApp c _ _ _) t r) | isClass c
  = let (css, t') = splitConstraints t in (css, RFun x tx t' r)
splitConstraints t
  = ([], t)
-------------------------------------------------------------------
-- | @instantiatePreds@ peels away the universally quantified @PVars@
--   of a @RType@, generates fresh @Ref@ for them and substitutes them
--   in the body.

instantiatePreds γ e (RAllP π t)
  = do r     <- freshPredRef γ e π
       instantiatePreds γ e $ replacePreds "consE" t [(π, r)]

instantiatePreds _ _ t0
  = return t0

-------------------------------------------------------------------
-- | @instantiateStrata@ generates fresh @Strata@ vars and substitutes
--   them inside the body of the type.

instantiateStrata ls t = substStrata t ls <$> mapM (\_ -> fresh) ls

substStrata t ls ls'   = F.substa f t
  where
    f x                = fromMaybe x $ L.lookup x su
    su                 = zip ls ls'

-------------------------------------------------------------------

cconsLazyLet γ (Let (NonRec x ex) e) t
  = do tx <- trueTy (varType x)
       γ' <- (γ, "Let NonRec") +++= (x', ex, tx)
       cconsE γ' e t
    where
       x' = F.symbol x

cconsLazyLet _ _ _
  = errorstar "Constraint.Generate.cconsLazyLet called on invalid inputs"

-------------------------------------------------------------------
-- | Type Synthesis -----------------------------------------------
-------------------------------------------------------------------
consE :: CGEnv -> Expr Var -> CG SpecType
-------------------------------------------------------------------

consE γ (Var x)
  = do t <- varRefType γ x
       addLocA (Just x) (loc γ) (varAnn γ x t)
       return t

consE γ (Lit c)
  = refreshVV $ uRType $ literalFRefType (emb γ) c

consE γ e'@(App e (Type τ))
  = do RAllT α te <- checkAll ("Non-all TyApp with expr", e) <$> consE γ e
       t          <- if isGeneric α te then freshTy_type TypeInstE e τ else trueTy τ
       addW        $ WfC γ t
       t'         <- refreshVV t
       instantiatePreds γ e' $ subsTyVar_meet' (α, t') te

consE γ e'@(App e a) | isDictionary a
  = if isJust tt
      then return $ fromJust tt
      else do ([], πs, ls, te) <- bkUniv <$> consE γ e
              te0              <- instantiatePreds γ e' $ foldr RAllP te πs
              te'              <- instantiateStrata ls te0
              (γ', te''')      <- dropExists γ te'
              te''             <- dropConstraints γ te'''
              updateLocA πs (exprLoc e) te''
              let RFun x tx t _ = checkFun ("Non-fun App with caller ", e') te''
              pushConsBind      $ cconsE γ' a tx
              addPost γ'        $ maybe (checkUnbound γ' e' x t) (F.subst1 t . (x,)) (argExpr γ a)
  where
    grepfunname (App x (Type _)) = grepfunname x
    grepfunname (Var x)          = x
    grepfunname e                = errorstar $ "grepfunname on \t" ++ showPpr e
    mdict w                      = case w of
                                     Var x    -> case dlookup (denv γ) x of {Just _ -> Just x; Nothing -> Nothing}
                                     Tick _ e -> mdict e
                                     _        -> Nothing
    isDictionary _               = isJust (mdict a)
    d = fromJust (mdict a)
    dinfo = dlookup (denv γ) d
    tt = dhasinfo dinfo $ grepfunname e

consE γ e'@(App e a)
  = do ([], πs, ls, te) <- bkUniv <$> consE γ e
       te0              <- instantiatePreds γ e' $ foldr RAllP te πs
       te'              <- instantiateStrata ls te0
       (γ', te''')      <- dropExists γ te'
       te''             <- dropConstraints γ te'''
       updateLocA πs (exprLoc e) te''
       let RFun x tx t _ = checkFun ("Non-fun App with caller ", e') te''
       pushConsBind      $ cconsE γ' a tx
       addPost γ'        $ maybe (checkUnbound γ' e' x t) (F.subst1 t . (x,)) (argExpr γ a)

consE γ (Lam α e) | isTyVar α
  = liftM (RAllT (rTyVar α)) (consE γ e)

consE γ  e@(Lam x e1)
  = do tx      <- freshTy_type LamE (Var x) τx
       γ'      <- ((γ, "consE") += (F.symbol x, tx))
       t1      <- consE γ' e1
       addIdA x $ AnnDef tx
       addW     $ WfC γ tx
       return   $ rFun (F.symbol x) tx t1
    where
      FunTy τx _ = exprType e

-- EXISTS-BASED CONSTRAINTS HEREHEREHEREHERE
-- Currently suppressed because they break all sorts of invariants,
-- e.g. for `unfoldR`...
-- consE γ e@(Let b@(NonRec x _) e')
--   = do γ'    <- consCBLet γ b
--        consElimE γ' [F.symbol x] e'
--
-- consE γ (Case e x _ [(ac, ys, ce)])
--   = do γ'  <- consCBLet γ (NonRec x e)
--        γ'' <- caseEnv γ' x [] ac ys
--        consElimE γ'' (F.symbol <$> (x:ys)) ce

consE γ e@(Let _ _)
  = cconsFreshE LetE γ e

consE γ e@(Case _ _ _ _)
  = cconsFreshE CaseE γ e

consE γ (Tick tt e)
  = do t <- consE (γ `setLoc` l) e
       addLocA Nothing l (AnnUse t)
       return t
    where l = tickSrcSpan tt

consE γ e@(Cast e' _)
  = castTy γ (exprType e) e'

consE _ e@(Coercion _)
   = trueTy $ exprType e

consE _ e@(Type t)
  = errorstar $ "consE cannot handle type" ++ showPpr (e, t)

castTy _ τ (Var x)
  = do t <- trueTy τ
       return $  t `strengthen` (uTop $ F.uexprReft $ F.expr x)

castTy γ τ e
  = do t <- trueTy (exprType e)
       cconsE γ e t
       trueTy τ

singletonReft = uTop . F.symbolReft . F.symbol

-- | @consElimE@ is used to *synthesize* types by **existential elimination**
--   instead of *checking* via a fresh template. That is, assuming
--      γ |- e1 ~> t1
--   we have
--      γ |- let x = e1 in e2 ~> Ex x t1 t2
--   where
--      γ, x:t1 |- e2 ~> t2
--   instead of the earlier case where we generate a fresh template `t` and check
--      γ, x:t1 |- e <~ t

-- consElimE γ xs e
--   = do t     <- consE γ e
--        xts   <- forM xs $ \x -> (x,) <$> (γ ??= x)
--        return $ rEx xts t

-- | @consFreshE@ is used to *synthesize* types with a **fresh template** when
--   the above existential elimination is not easy (e.g. at joins, recursive binders)

cconsFreshE kvkind γ e
  = do t   <- freshTy_type kvkind e $ exprType e
       addW $ WfC γ t
       cconsE γ e t
       return t

checkUnbound γ e x t
  | x `notElem` (F.syms t)
  = t
  | otherwise
  = errorstar $ "checkUnbound: " ++ show x ++ " is elem of syms of " ++ show t
                 ++ "\nIn\t"  ++ showPpr e ++ " at " ++ showPpr (loc γ)

dropExists γ (REx x tx t) = liftM (, t) $ (γ, "dropExists") += (x, tx)
dropExists γ t            = return (γ, t)

dropConstraints :: CGEnv -> SpecType -> CG SpecType
dropConstraints γ (RFun x tx@(RApp c _ _ _) t r) | isClass c
  = (flip (RFun x tx)) r <$> dropConstraints γ t
dropConstraints γ (RRTy cts _ OCons t)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("splitS", x,t)) γ xts
       addC (SubC  γ' t1 t2)  "dropConstraints"
       dropConstraints γ t
  where
    (xts, t1, t2) = envToSub cts

dropConstraints _ t = return t

-------------------------------------------------------------------------------------
cconsCase :: CGEnv -> Var -> SpecType -> [AltCon] -> (AltCon, [Var], CoreExpr) -> CG ()
-------------------------------------------------------------------------------------
cconsCase γ x t acs (ac, ys, ce)
  = do cγ <- caseEnv γ x acs ac ys
       cconsE cγ ce t

refreshTy t = refreshVV t >>= refreshArgs

refreshVV (RAllT a t) = liftM (RAllT a) (refreshVV t)
refreshVV (RAllP p t) = liftM (RAllP p) (refreshVV t)

refreshVV (REx x t1 t2)
  = do [t1', t2'] <- mapM refreshVV [t1, t2]
       liftM (shiftVV (REx x t1' t2')) fresh

refreshVV (RFun x t1 t2 r)
  = do [t1', t2'] <- mapM refreshVV [t1, t2]
       liftM (shiftVV (RFun x t1' t2' r)) fresh

refreshVV (RAppTy t1 t2 r)
  = do [t1', t2'] <- mapM refreshVV [t1, t2]
       liftM (shiftVV (RAppTy t1' t2' r)) fresh

refreshVV (RApp c ts rs r)
  = do ts' <- mapM refreshVV ts
       rs' <- mapM refreshVVRef rs
       liftM (shiftVV (RApp c ts' rs' r)) fresh

refreshVV t
  = return t


refreshVVRef (RProp ss t)
  = do xs    <- mapM (\_ -> fresh) (fst <$> ss)
       let su = F.mkSubst $ zip (fst <$> ss) (F.EVar <$> xs)
       liftM (RProp (zip xs (snd <$> ss)) . F.subst su) (refreshVV t)

refreshVVRef (RPropP ss r)
  = return $ RPropP ss r

refreshVVRef (RHProp _ _)
  = errorstar "TODO: EFFECTS refreshVVRef"


-------------------------------------------------------------------------------------
caseEnv   :: CGEnv -> Var -> [AltCon] -> AltCon -> [Var] -> CG CGEnv
-------------------------------------------------------------------------------------
caseEnv γ x _   (DataAlt c) ys
  = do let (x' : ys')    = F.symbol <$> (x:ys)
       xt0              <- checkTyCon ("checkTycon cconsCase", x) <$> γ ??= x'
       tdc              <- γ ??= (dataConSymbol c) >>= refreshVV
       let (rtd, yts, _) = unfoldR tdc (shiftVV xt0 x') ys
       let r1            = dataConReft   c   ys'
       let r2            = dataConMsReft rtd ys'
       let xt            = (xt0 `F.meet` rtd) `strengthen` (uTop (r1 `F.meet` r2))
       let cbs           = safeZip "cconsCase" (x':ys') (xt0:yts)
       cγ'              <- addBinders γ x' cbs
       cγ               <- addBinders cγ' x' [(x', xt)]
       return cγ

caseEnv γ x acs a _
  = do let x'  = F.symbol x
       xt'    <- (`strengthen` uTop (altReft γ acs a)) <$> (γ ??= x')
       cγ     <- addBinders γ x' [(x', xt')]
       return cγ

altReft γ _ (LitAlt l)   = literalFReft (emb γ) l
altReft γ acs DEFAULT    = mconcat [notLiteralReft l | LitAlt l <- acs]
  where notLiteralReft   = maybe mempty F.notExprReft . snd . literalConst (emb γ)
altReft _ _ _            = error "Constraint : altReft"

unfoldR td (RApp _ ts rs _) ys = (t3, tvys ++ yts, ignoreOblig rt)
  where
        tbody              = instantiatePvs (instantiateTys td ts) $ reverse rs
        (ys0, yts', _, rt) = safeBkArrow $ instantiateTys tbody tvs'
        yts''              = zipWith F.subst sus (yts'++[rt])
        (t3,yts)           = (last yts'', init yts'')
        sus                = F.mkSubst <$> (L.inits [(x, F.EVar y) | (x, y) <- zip ys0 ys'])
        (αs, ys')          = mapSnd (F.symbol <$>) $ L.partition isTyVar ys
        tvs'               = rVar <$> αs
        tvys               = ofType . varType <$> αs

unfoldR _  _                _  = error "Constraint.hs : unfoldR"

instantiateTys = foldl' go
  where go (RAllT α tbody) t = subsTyVar_meet' (α, t) tbody
        go _ _               = errorstar "Constraint.instanctiateTy"

instantiatePvs = foldl' go
  where go (RAllP p tbody) r = replacePreds "instantiatePv" tbody [(p, r)]
        go _ _               = errorstar "Constraint.instanctiatePv"

checkTyCon _ t@(RApp _ _ _ _) = t
checkTyCon x t                = checkErr x t --errorstar $ showPpr x ++ "type: " ++ showPpr t

checkFun _ t@(RFun _ _ _ _)   = t
checkFun x t                  = checkErr x t

checkAll _ t@(RAllT _ _)      = t
checkAll x t                  = checkErr x t

checkErr (msg, e) t          = errorstar $ msg ++ showPpr e ++ ", type: " ++ showpp t

varAnn γ x t
  | x `S.member` recs γ
  = AnnLoc (getSrcSpan' x)
  | otherwise
  = AnnUse t

getSrcSpan' x
  | loc == noSrcSpan
  = loc
  | otherwise
  = loc
  where loc = getSrcSpan x

-----------------------------------------------------------------------
-- | Helpers: Creating Fresh Refinement -------------------------------
-----------------------------------------------------------------------

freshPredRef :: CGEnv -> CoreExpr -> PVar RSort -> CG SpecProp
freshPredRef γ e (PV _ (PVProp τ) _ as)
  = do t    <- freshTy_type PredInstE e (toType τ)
       args <- mapM (\_ -> fresh) as
       let targs = [(x, s) | (x, (s, y, z)) <- zip args as, (F.EVar y) == z ]
       γ' <- foldM (++=) γ [("freshPredRef", x, ofRSort τ) | (x, τ) <- targs]
       addW $ WfC γ' t
       return $ RProp targs t

freshPredRef _ _ (PV _ PVHProp _ _)
  = errorstar "TODO:EFFECTS:freshPredRef"

-----------------------------------------------------------------------
---------- Helpers: Creating Refinement Types For Various Things ------
-----------------------------------------------------------------------

argExpr :: CGEnv -> CoreExpr -> Maybe F.Expr
argExpr _ (Var vy)    = Just $ F.eVar vy
argExpr γ (Lit c)     = snd  $ literalConst (emb γ) c
argExpr γ (Tick _ e)  = argExpr γ e
argExpr _ e           = errorstar $ "argExpr: " ++ showPpr e


varRefType γ x = liftM (varRefType' γ x) (γ ??= F.symbol x)

varRefType' γ x t'
  | Just tys <- trec γ, Just tr <- M.lookup x' tys
  = tr `strengthen` xr
  | otherwise
  = t
  where t  = t' `strengthen` xr
        xr = singletonReft x -- uTop $ F.symbolReft $ F.symbol x
        x' = F.symbol x

-- TODO: should only expose/use subt. Not subsTyVar_meet
subsTyVar_meet' (α, t) = subsTyVar_meet (α, toRSort t, t)

-----------------------------------------------------------------------
--------------- Forcing Strictness ------------------------------------
-----------------------------------------------------------------------

instance NFData CGEnv where
  rnf (CGE x1 x2 x3 _ x5 x6 x7 x8 x9 _ _ x10 _ _ _ _ _)
    = x1 `seq` rnf x2 `seq` seq x3 `seq` rnf x5 `seq`
      rnf x6  `seq` x7 `seq` rnf x8 `seq` rnf x9 `seq` rnf x10

instance NFData FEnv where
  rnf (FE x1 _) = rnf x1

instance NFData SubC where
  rnf (SubC x1 x2 x3)
    = rnf x1 `seq` rnf x2 `seq` rnf x3
  rnf (SubR x1 _ x2)
    = rnf x1 `seq` rnf x2

instance NFData Class where
  rnf _ = ()

instance NFData RTyCon where
  rnf _ = ()

instance NFData Type where
  rnf _ = ()

instance NFData WfC where
  rnf (WfC x1 x2)
    = rnf x1 `seq` rnf x2

instance NFData CGInfo where
  rnf x = ({-# SCC "CGIrnf1" #-}  rnf (hsCs x))       `seq`
          ({-# SCC "CGIrnf2" #-}  rnf (hsWfs x))      `seq`
          ({-# SCC "CGIrnf3" #-}  rnf (fixCs x))      `seq`
          ({-# SCC "CGIrnf4" #-}  rnf (fixWfs x))     `seq`
          ({-# SCC "CGIrnf6" #-}  rnf (freshIndex x)) `seq`
          ({-# SCC "CGIrnf7" #-}  rnf (binds x))      `seq`
          ({-# SCC "CGIrnf8" #-}  rnf (annotMap x))   `seq`
          ({-# SCC "CGIrnf10" #-} rnf (kuts x))       `seq`
          ({-# SCC "CGIrnf10" #-} rnf (lits x))       `seq`
          ({-# SCC "CGIrnf10" #-} rnf (kvProf x))

-------------------------------------------------------------------------------
--------------------- Reftypes from F.Fixpoint Expressions ----------------------
-------------------------------------------------------------------------------

forallExprRefType     :: CGEnv -> SpecType -> SpecType
forallExprRefType γ t = t `strengthen` (uTop r')
  where
    r'                = fromMaybe mempty $ forallExprReft γ r
    r                 = F.sr_reft $ rTypeSortedReft (emb γ) t

forallExprReft :: CGEnv -> F.Reft -> Maybe F.Reft
forallExprReft γ r = F.isSingletonReft r >>= forallExprReft_ γ

--   = do e  <- F.isSingletonReft r
--        r' <- forallExprReft_ γ e
--        return r'

forallExprReft_ :: CGEnv -> F.Expr -> Maybe F.Reft
forallExprReft_ γ (F.EApp f es)
  = case forallExprReftLookup γ (val f) of
      Just (xs,_,_,t) -> let su = F.mkSubst $ safeZip "fExprRefType" xs es in
                       Just $ F.subst su $ F.sr_reft $ rTypeSortedReft (emb γ) t
      Nothing       -> Nothing -- F.exprReft e

forallExprReft_ γ (F.EVar x)
  = case forallExprReftLookup γ x of
      Just (_,_,_,t)  -> Just $ F.sr_reft $ rTypeSortedReft (emb γ) t
      Nothing       -> Nothing -- F.exprReft e

forallExprReft_ _ _ = Nothing -- F.exprReft e

forallExprReftLookup γ x = snap <$> F.lookupSEnv x (syenv γ)
  where
    snap                 = mapFourth4 ignoreOblig . bkArrow . fourth4 . bkUniv . (γ ?=) . F.symbol

{-
splitExistsCases z xs tx
  = fmap $ fmap (exrefAddEq z xs tx)

exrefAddEq z xs t (F.Reft (s, F.Refa rs))
  = F.Reft(s, F.Refa (F.POr [ pand x | x <- xs]))
  where
    tref      = fromMaybe mempty $ stripRTypeBase t
    pand x    = substzx x rs `mappend` exrefToPred x tref
    substzx x = F.subst (F.mkSubst [(z, F.EVar x)])

exrefToPred x u             = F.subst (F.mkSubst [(v, F.EVar x)]) p
  where
    F.Reft (v, F.Refa p)    = ur_reft u
-}

-------------------------------------------------------------------------------
-------------------- Cleaner Signatures For Rec-bindings ----------------------
-------------------------------------------------------------------------------

exprLoc                         :: CoreExpr -> Maybe SrcSpan

exprLoc (Tick tt _)             = Just $ tickSrcSpan tt
exprLoc (App e a) | isType a    = exprLoc e
exprLoc _                       = Nothing

isType (Type _)                 = True
isType a                        = eqType (exprType a) predType


exprRefType :: CoreExpr -> SpecType
exprRefType = exprRefType_ M.empty

exprRefType_ :: M.HashMap Var SpecType -> CoreExpr -> SpecType
exprRefType_ γ (Let b e)
  = exprRefType_ (bindRefType_ γ b) e

exprRefType_ γ (Lam α e) | isTyVar α
  = RAllT (rTyVar α) (exprRefType_ γ e)

exprRefType_ γ (Lam x e)
  = rFun (F.symbol x) (ofType $ varType x) (exprRefType_ γ e)

exprRefType_ γ (Tick _ e)
  = exprRefType_ γ e

exprRefType_ γ (Var x)
  = M.lookupDefault (ofType $ varType x) x γ

exprRefType_ _ e
  = ofType $ exprType e

bindRefType_ γ (Rec xes)
  = extendγ γ [(x, exprRefType_ γ e) | (x,e) <- xes]

bindRefType_ γ (NonRec x e)
  = extendγ γ [(x, exprRefType_ γ e)]

extendγ γ xts
  = foldr (\(x,t) m -> M.insert x t m) γ xts


instance NFData REnv where
  rnf (REnv _) = () -- rnf m
