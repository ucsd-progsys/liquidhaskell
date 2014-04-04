module Language.Haskell.Liquid.Qualifier (
  specificationQualifiers
  ) where

import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.GhcInterface
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
  = [ q | (x, t) <- tySigs $ spec info
        , x `S.member` (S.fromList $ defVars info)
        , q <- refTypeQuals (tcEmbeds $ spec info) (val t)
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


refTypeQuals tce t = quals ++ 
    [ pAppQual tce p args (v, expr) 
    | p            <- preds
    , (s, v, _)    <- pargs p
    , (args, expr) <- concatMap (expressionsOfSort (rTypeSort tce s)) quals
    ]  
    where 
      quals        = refTypeQuals' tce t
      preds        = ty_preds $ toRTypeRep t

expressionsOfSort sort (Q _ pars (PAtom Eq (EVar v) e2)) 
  | (v, sort) `elem` pars
  = [(filter (/=(v, sort)) pars, e2)]

expressionsOfSort _ _  
  = [] 

pAppQual tce p args (v, expr) =  Q "Auto" freeVars pred
  where 
    freeVars                  = (vv, tyvv) : (predv, typred) : args
    pred                      = pApp predv $ EVar vv:predArgs
    vv                        = S "v"
    predv                     = S "~P"
    tyvv                      = rTypeSort tce $ ptype p
    typred                    = rTypeSort tce (toPredType p :: RRType ())
    predArgs                  = mkexpr <$> (snd3 <$> pargs p)
    mkexpr x                  = if x == v then expr else EVar x 

-- refTypeQuals :: SpecType -> [Qualifier] 
refTypeQuals' tce t0          = go emptySEnv t0
  where 
    go γ t@(RVar _ _)         = refTopQuals tce t0 γ t     
    go γ (RAllT _ t)          = go γ t 
    go γ (RAllP _ t)          = go γ t 
    go γ (RFun x t t' _)      = (go γ t) 
                                ++ (go (insertSEnv x (rTypeSort tce t) γ) t')
    go γ t@(RApp c ts rs _)   = (refTopQuals tce t0 γ t) 
                                ++ concatMap (go (insertSEnv (rTypeValueVar t) (rTypeSort tce t) γ)) ts 
                                ++ goRefs c (insertSEnv (rTypeValueVar t) (rTypeSort tce t) γ) rs 
    go γ (RAllE x t t')       = (go γ t) 
                                ++ (go (insertSEnv x (rTypeSort tce t) γ) t')
    go γ (REx x t t')         = (go γ t) 
                                ++ (go (insertSEnv x (rTypeSort tce t) γ) t')
    go _ _                    = []
    goRefs c γ rs             = concat $ zipWith (goRef γ) rs (rTyConPs c)
    goRef γ (RPoly s t)  _    = go (insertsSEnv γ s) t
    goRef _ (RMono _ _)  _    = []
    insertsSEnv               = foldr (\(x, t) γ -> insertSEnv x (rTypeSort tce t) γ)

refTopQuals tce t0 γ t 
  = [ mkQual t0 γ v so pa | let (RR so (Reft (v, ras))) = rTypeSortedReft tce t 
                          , RConc p                    <- ras                 
                          , pa                         <- atoms p
    ] ++
    [ mkPQual tce t0 γ s e | let (U _ (Pr ps) _) = fromMaybe (msg t) $ stripRTypeBase t
                           , p <- (findPVar (ty_preds $ toRTypeRep t0)) <$> ps
                           , (s, _, e) <- pargs p
    ] 
    where 
      msg t = errorstar $ "Qualifier.refTopQuals: no typebase" ++ showpp t

mkPQual tce t0 γ t e = mkQual t0 γ' v so pa
  where 
    v                = S "vv"
    so               = rTypeSort tce t
    γ'               = insertSEnv v so γ
    pa               = PAtom Eq (EVar v) e   

mkQual t0 γ v so p = Q "Auto" ((v, so) : yts) p'
  where 
    yts            = [(y, lookupSort t0 x γ) | (x, y) <- xys ]
    p'             = subst (mkSubst (second EVar <$> xys)) p
    xys            = zipWith (\x i -> (x, S ("~A" ++ show i))) xs [0..] 
    xs             = delete v $ orderedFreeVars γ p

lookupSort t0 x γ  = fromMaybe (errorstar msg) $ lookupSEnv x γ 
  where 
    msg            = "Unknown freeVar " ++ show x ++ " in specification " ++ show t0

orderedFreeVars γ = nub . filter (`memberSEnv` γ) . syms 

atoms (PAnd ps)   = concatMap atoms ps
atoms p           = [p]


