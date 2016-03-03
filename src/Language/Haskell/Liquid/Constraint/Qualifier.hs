{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Language.Haskell.Liquid.Constraint.Qualifier (
  specificationQualifiers
  ) where

import TyCon

import Prelude hiding (error)

import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.GHC.Misc  (getSourcePos)
import Language.Haskell.Liquid.Types.PredType
import Language.Haskell.Liquid.Types
import Language.Fixpoint.Types



-- import Control.Applicative      ((<$>))
import Data.List                (delete, nub)
import Data.Maybe               (catMaybes, fromMaybe)
import qualified Data.HashSet as S
-- import Data.Bifunctor           (second)
import Debug.Trace

-----------------------------------------------------------------------------------
specificationQualifiers :: Int -> GhcInfo -> SEnv Sort -> [Qualifier]
-----------------------------------------------------------------------------------
specificationQualifiers k info lEnv
  = [ q | (x, t) <- (tySigs $ spec info) ++ (asmSigs $ spec info) ++ (ctors $ spec info)
        , x `S.member` (S.fromList $ defVars info ++
                                     -- NOTE: this mines extra, useful qualifiers but causes
                                     -- a significant increase in running time, so we hide it
                                     -- behind `--scrape-imports` and `--scrape-used-imports`
                                     if info `hasOpt` scrapeUsedImports
                                     then useVars info
                                     else if info `hasOpt` scrapeImports
                                     then impVars info
                                     else [])
        , q <- refTypeQuals lEnv (getSourcePos x) (tcEmbeds $ spec info) (val t)
        -- NOTE: large qualifiers are VERY expensive, so we only mine
        -- qualifiers up to a given size, controlled with --max-params
        , length (q_params q) <= k + 1
    ]
    -- where lEnv = trace ("Literals: " ++ show lEnv') lEnv'

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
refTypeQuals :: SEnv Sort -> SourcePos -> TCEmb TyCon -> SpecType -> [Qualifier]
refTypeQuals lEnv l tce t0    = go emptySEnv t0
  where
    scrape                    = refTopQuals lEnv l tce t0
    add x t γ                 = insertSEnv x (rTypeSort tce t) γ
    goBind x t γ t'           = go (add x t γ) t'
    go γ t@(RVar _ _)         = scrape γ t
    go γ (RAllT _ t)          = go γ t
    go γ (RAllP p t)          = go (insertSEnv (pname p) (rTypeSort tce $ (pvarRType p :: RSort)) γ) t
    go γ t@(RAppTy t1 t2 _)   = go γ t1 ++ go γ t2 ++ scrape γ t
    go γ (RFun x t t' _)      = go γ t ++ goBind x t γ t'
    go γ t@(RApp c ts rs _)   = scrape γ t ++ concatMap (go γ') ts ++ goRefs c γ' rs
                                where γ' = add (rTypeValueVar t) t γ
    go γ (RAllE x t t')       = go γ t ++ goBind x t γ t'
    go γ (REx x t t')         = go γ t ++ goBind x t γ t'
    go _ _                    = []
    goRefs c g rs             = concat $ zipWith (goRef g) rs (rTyConPVs c)
    goRef _ (RProp _ (RHole _)) _ = []
    goRef g (RProp s t)  _    = go (insertsSEnv g s) t
    insertsSEnv               = foldr (\(x, t) γ -> insertSEnv x (rTypeSort tce t) γ)

refTopQuals lEnv l tce t0 γ t
  = [ mkQ v so pa  | let (RR so (Reft (v, ra))) = rTypeSortedReft tce t
                                  , pa                        <- conjuncts ra
                                  , not $ isHole pa
    ]
    ++
    [ mkP s e | let (MkUReft _ (Pr ps) _) = fromMaybe (msg t) $ stripRTypeBase t
                             , p <- findPVar (ty_preds $ toRTypeRep t0) <$> ps
                             , (s, _, e) <- pargs p
    ]
    where
      mkQ   = mkQual  lEnv l     t0 γ
      mkP   = mkPQual lEnv l tce t0 γ
      msg t = panic Nothing $ "Qualifier.refTopQuals: no typebase" ++ showpp t

mkPQual lEnv l tce t0 γ t e = mkQual lEnv l t0 γ' v so pa
  where
    v                  = "vv"
    so                 = rTypeSort tce t
    γ'                 = insertSEnv v so γ
    pa                 = PAtom Eq (EVar v) e

mkQual = mkQualNEW

mkQualNEW lEnv l _ γ v so p   = Q "Auto" ((v, so) : xts) p l
  where
    xs   = delete v $ nub $ syms p
    xts = catMaybes $ zipWith (envSort l lEnv γ) xs [0..]
    -- xts  = Language.Fixpoint.Misc.traceShow msg $ xts'
    -- msg  = "Free Vars in: " ++ showFix p ++ " in " ++ show t0

-- OLD
{-
  TODO: If it's so OLD, do we need to keep it? Never called, etc...
mkQualOLD lEnv l t0 γ v so p   = Q "Auto" ((v, so) : yts) p' l
  where
    yts                = [(y, lookupSort l γ i x) | (x, i, y) <- xys ]
    p'                 = subst su p
    su                 = mkSubst [(x, EVar y) | (x, _, y) <- xys]
    xys                = zipWith (\x i -> (x, i, symbol ("~A" ++ show i))) xs [0..]
    -- xs                 = delete v $ orderedFreeVars γ p
    xs                 = {- Language.Fixpoint.Misc.traceShow msg $ -} delete v $ orderedFreeVarsOLD γ p
    msg                = "Free Vars in: " ++ showFix p ++ " in " ++ show t0

orderedFreeVarsOLD :: SEnv Sort -> Pred -> [Symbol]
orderedFreeVarsOLD γ = nub . filter (`memberSEnv` γ) . syms
-}

{-
   TODO: Never used, do I need to exist?
orderedFreeVars :: SEnv Sort -> Pred -> [Symbol]
orderedFreeVars lEnv = nub . filter (not . (`memberSEnv` lEnv)) . syms
-}

envSort :: SourcePos -> SEnv Sort -> SEnv Sort -> Symbol -> Integer -> Maybe (Symbol, Sort)
envSort l lEnv tEnv x i
  | Just t <- lookupSEnv x tEnv = Just (x, t)
  | Just _ <- lookupSEnv x lEnv = Nothing
  | otherwise                   = Just (x, ai)
  where
    ai             = trace msg $ fObj $ Loc l l $ tempSymbol "LHTV" i
    msg            = "unknown symbol in qualifier: " ++ show x

{-
   TODO: Never used, do I need to exist?
lookupSort l γ i x = fromMaybe ai $ lookupSEnv x γ
  where
    ai             = trace msg $ fObj $ Loc l l $ tempSymbol "LHTV" i
    msg            = "unknown symbol in qualifier: " ++ show x
-}
