{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
module Language.Haskell.Liquid.Qualifier (
  specificationQualifiers
  ) where

import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.GhcMisc  (getSourcePos)
import Language.Haskell.Liquid.PredType
import Language.Haskell.Liquid.Types
import Language.Fixpoint.Types
import Language.Fixpoint.Misc

import Control.Applicative      ((<$>))
import Data.List                (delete, nub)
import Data.Maybe               (fromMaybe)
import qualified Data.HashSet as S
import Data.Bifunctor           (second) 

-----------------------------------------------------------------------------------
specificationQualifiers :: Int -> GhcInfo -> [Qualifier]
-----------------------------------------------------------------------------------
specificationQualifiers k info
  = [ q | (x, t) <- (tySigs $ spec info) ++ (asmSigs $ spec info) ++ (ctors $ spec info)
        -- FIXME: this mines extra, useful qualifiers but causes a significant increase in running time
        -- , ((isClassOp x || isDataCon x) && x `S.member` (S.fromList $ impVars info ++ defVars info)) || x `S.member` (S.fromList $ defVars info)
        , x `S.member` (S.fromList $ defVars info)
        , q <- refTypeQuals (getSourcePos x) (tcEmbeds $ spec info) (val t)
        , length (q_params q) <= k + 1
    ]

-- GRAVEYARD: scraping quals from imports kills the system with too much crap
-- specificationQualifiers info = {- filter okQual -} qs 
--   where
--     qs                       = concatMap refTypeQualifiers ts 
--     refTypeQualifiers        = refTypeQuals $ tcEmbeds spc 
--     ts                       = val <$> t1s ++ t2s 
--     t1s                      = [t | (x, t) <- tySigs spc, x `S.member` definedVars] 
--     t2s                      = [] -- [t | (_, t) <- ctor spc                            ]
--     definedVars              = S.fromList $ defVars info
--     spc                      = spec info
-- 
-- okQual                       = not . any isPred . map snd . q_params 
--   where
--     isPred (FApp tc _)       = tc == stringFTycon "Pred" 
--     isPred _                 = False


refTypeQuals l tce t  = quals ++ pAppQuals l tce preds quals 
  where 
    quals             = refTypeQuals' l tce t
    preds             = filter isPropPV $ ty_preds $ toRTypeRep t

pAppQuals l tce ps qs = [ pAppQual l tce p xs (v, e) | p <- ps, (s, v, _) <- pargs p, (xs, e) <- mkE s ]
  where
    mkE s             = concatMap (expressionsOfSort (rTypeSort tce s)) qs

expressionsOfSort sort (Q _ pars (PAtom Eq (EVar v) e2) _) 
  | (v, sort) `elem` pars
  = [(filter (/=(v, sort)) pars, e2)]

expressionsOfSort _ _  
  = [] 

pAppQual l tce p args (v, expr) =  Q "Auto" freeVars pred l
  where 
    freeVars                  = (vv, tyvv) : (predv, typred) : args
    pred                      = pApp predv $ EVar vv:predArgs
    vv                        = "v"
    predv                     = "~P"
    tyvv                      = rTypeSort tce $ pvType p
    typred                    = rTypeSort tce (pvarRType p :: RSort)
    predArgs                  = mkexpr <$> (snd3 <$> pargs p)
    mkexpr x                  = if x == v then expr else EVar x 

-- refTypeQuals :: SpecType -> [Qualifier] 
refTypeQuals' l tce t0        = go emptySEnv t0
  where 
    go γ t@(RVar _ _)         = refTopQuals l tce t0 γ t     
    go γ (RAllT _ t)          = go γ t 
    go γ (RAllP _ t)          = go γ t 
    go γ t@(RAppTy t1 t2 _)   = go γ t1 ++ go γ t2 ++ refTopQuals l tce t0 γ t
    go γ (RFun x t t' _)      = (go γ t) 
                                ++ (go (insertSEnv x (rTypeSort tce t) γ) t')
    go γ t@(RApp c ts rs _)   = (refTopQuals l tce t0 γ t) 
                                ++ concatMap (go (insertSEnv (rTypeValueVar t) (rTypeSort tce t) γ)) ts 
                                ++ goRefs c (insertSEnv (rTypeValueVar t) (rTypeSort tce t) γ) rs 
    go γ (RAllE x t t')       = (go γ t) 
                                ++ (go (insertSEnv x (rTypeSort tce t) γ) t')
    go γ (REx x t t')         = (go γ t) 
                                ++ (go (insertSEnv x (rTypeSort tce t) γ) t')
    go _ _                    = []
    goRefs c g rs             = concat $ zipWith (goRef g) rs (rTyConPVs c)
    goRef g (RProp  s t)  _   = go (insertsSEnv g s) t
    goRef _ (RPropP _ _)  _   = []
    goRef _ (RHProp _ _)  _   = errorstar "TODO: EFFECTS"
    insertsSEnv               = foldr (\(x, t) γ -> insertSEnv x (rTypeSort tce t) γ)

refTopQuals l tce t0 γ t 
  = [ mkQual l t0 γ v so pa  | let (RR so (Reft (v, ras))) = rTypeSortedReft tce t 
                             , RConc p                    <- ras                 
                             , pa                         <- atoms p
    ] ++
    [ mkPQual l tce t0 γ s e | let (U _ (Pr ps) _) = fromMaybe (msg t) $ stripRTypeBase t
                             , p <- (findPVar (ty_preds $ toRTypeRep t0)) <$> ps
                             , (s, _, e) <- pargs p
    ] 
    where 
      msg t = errorstar $ "Qualifier.refTopQuals: no typebase" ++ showpp t

mkPQual l tce t0 γ t e = mkQual l t0 γ' v so pa
  where 
    v                  = "vv"
    so                 = rTypeSort tce t
    γ'                 = insertSEnv v so γ
    pa                 = PAtom Eq (EVar v) e   

mkQual l t0 γ v so p   = Q "Auto" ((v, so) : yts) p' l 
  where 
    yts                = [(y, lookupSort t0 x γ) | (x, y) <- xys ]
    p'                 = subst (mkSubst (second EVar <$> xys)) p
    xys                = zipWith (\x i -> (x, symbol ("~A" ++ show i))) xs [0..]
    xs                 = delete v $ orderedFreeVars γ p

lookupSort t0 x γ  = fromMaybe (errorstar msg) $ lookupSEnv x γ 
  where 
    msg            = "Unknown freeVar " ++ show x ++ " in specification " ++ show t0

orderedFreeVars γ = nub . filter (`memberSEnv` γ) . syms 

atoms (PAnd ps)   = concatMap atoms ps
atoms p           = [p]


