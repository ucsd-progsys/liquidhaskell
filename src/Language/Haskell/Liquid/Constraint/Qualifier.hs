{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Language.Haskell.Liquid.Constraint.Qualifier (
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
specificationQualifiers :: Int -> GhcInfo -> SEnv Sort -> [Qualifier]
-----------------------------------------------------------------------------------
specificationQualifiers k info lEnv
  = [ q | (x, t) <- (tySigs $ spec info) ++ (asmSigs $ spec info) ++ (ctors $ spec info)
        -- FIXME: this mines extra, useful qualifiers but causes a significant increase in running time
        -- , ((isClassOp x || isDataCon x) && x `S.member` (S.fromList $ impVars info ++ defVars info)) || x `S.member` (S.fromList $ defVars info)
        , x `S.member` (S.fromList $ defVars info)
        , q <- refTypeQuals lEnv (getSourcePos x) (tcEmbeds $ spec info) (val t)
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


-- TODO: rewrite using foldReft'
-- refTypeQuals :: SpecType -> [Qualifier]
refTypeQuals :: SEnv Sort -> _ -> _ -> SpecType -> [Qualifier]
refTypeQuals lEnv l tce t0    = go emptySEnv t0
  where
    scrape                    = refTopQuals lEnv l tce t0
    go γ t@(RVar _ _)         = scrape γ t
    go γ (RAllT _ t)          = go γ t
    go γ (RAllP p t)          = go (insertSEnv (pname p) (rTypeSort tce $ (pvarRType p :: RSort)) γ) t
    go γ t@(RAppTy t1 t2 _)   = go γ t1 ++ go γ t2 ++ scrape γ t
    go γ (RFun x t t' _)      = (go γ t)
                                ++ (go (insertSEnv x (rTypeSort tce t) γ) t')
    go γ t@(RApp c ts rs _)   = (scrape γ t)
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

refTopQuals lEnv l tce t0 γ t
  = [ mkQ v so pa  | let (RR so (Reft (v, ra))) = rTypeSortedReft tce t
                                  , pa                        <- conjuncts ra
                                  , not $ isHole pa
    ]
    ++
    [ mkP s e | let (U _ (Pr ps) _) = fromMaybe (msg t) $ stripRTypeBase t
                             , p <- findPVar (ty_preds $ toRTypeRep t0) <$> ps
                             , (s, _, e) <- pargs p
    ]
    where
      mkQ   = mkQual lEnv l t0 γ
      mkP   = mkPQual lEnv l tce t0 γ
      msg t = errorstar $ "Qualifier.refTopQuals: no typebase" ++ showpp t

mkPQual lEnv l tce t0 γ t e = mkQual lEnv l t0 γ' v so pa
  where
    v                  = "vv"
    so                 = rTypeSort tce t
    γ'                 = insertSEnv v so γ
    pa                 = PAtom Eq (EVar v) e

mkQual lEnv l t0 γ v so p   = Q "Auto" ((v, so) : yts) p' l
  where
    yts                = [(y, lookupSort l γ i x) | (x, i, y) <- xys ]
    p'                 = subst su p
    su                 = mkSubst [(x, EVar y) | (x, _, y) <- xys]
    xys                = zipWith (\x i -> (x, i, symbol ("~A" ++ show i))) xs [0..]
    -- xs                 = delete v $ orderedFreeVars γ p
    xs                 = delete v $ orderedFreeVars lEnv p

orderedFreeVars :: SEnv Sort -> Pred -> [Symbol]
orderedFreeVars lEnv = nub . filter (not . (`memberSEnv` lEnv)) . syms

lookupSort l γ i x = fromMaybe ai $ lookupSEnv x γ
  where
    ai           = fObj $ Loc l l $ tempSymbol "LHTV" i


-- HEREHEREHERE
-- lookupSort γ i x = fromMaybe (errorstar msg) $ lookupSEnv x γ
--  where
--     msg          = "Unknown freeVar " ++ show x ++ " in specification " ++ show t0


-- atoms (PAnd ps)   = concatMap atoms ps
-- atoms p           = [p]
