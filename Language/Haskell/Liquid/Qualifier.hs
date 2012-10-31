module Language.Haskell.Liquid.Qualifier (
    Qualifier 
  , specificationQualifiers
  ) where

import Outputable

import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.GhcInterface
import Language.Haskell.Liquid.Fixpoint
import Language.Haskell.Liquid.GhcMisc
import Language.Haskell.Liquid.Misc

import Control.DeepSeq
import Control.Applicative      ((<$>))
import Data.List                (delete, nub)
import Data.Maybe               (fromMaybe)
import qualified Data.HashSet as S
import Data.Bifunctor           (second) 

data Qualifier = Q String           --nam
                   [(Symbol, Sort)] --params
                   Pred             --pred
               deriving (Eq, Ord) -- , Data, Typeable)

instance Fixpoint Qualifier where 
  toFix = pprQual

instance Outputable Qualifier where
  ppr   = pprQual

instance NFData Qualifier where
  rnf (Q x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3

pprQual (Q n xts p) = text "qualif" <+> text n <> parens args  <> colon <+> toFix p 
  where args = intersperse comma (toFix <$> xts)

------------------------------------------------------------------------------------
------------------------------------------------------------------------------------
------------------------------------------------------------------------------------

specificationQualifiers :: GhcInfo -> [Qualifier] 
specificationQualifiers info  
  = [ q | (x, t) <- tySigs $ spec info, x `S.member` xs, q <- refTypeQuals tce t
    ] where xs  = S.fromList $ defVars info
            tce = tcEmbeds   $ spec info

-- refTypeQuals :: SpecType -> [Qualifier] 
refTypeQuals tce t0 = go emptySEnv t0
  where go γ t@(RVar _ _)         = refTopQuals tce t0 γ t     
        go γ (RAllT _ t)          = go γ t 
        go γ (RAllP _ t)          = go γ t 
        go γ (RFun x t t' _)      = (go γ t) ++ (go (insertSEnv x (rTypeSort tce t) γ) t')
        go γ t@(RApp _ ts _ _)    = (refTopQuals tce t0 γ t) ++ concatMap (go γ) ts 
        go γ (REx x t t' )        = (go γ t) ++ (go (insertSEnv x (rTypeSort tce t) γ) t')
        go _ _                    = []

refTopQuals tce t0 γ t 
  = [ mkQual t0 γ v so pa | let (RR so (Reft (v, ras))) = rTypeSortedReft tce t 
                          , RConc p                    <- ras                 
                          , pa                         <- atoms p
    ]

mkQual t0 γ v so p = Q "Auto" ((v, so) : yts) p'
  where yts  = [(y, lookupSort t0 x γ) | (x, y) <- xys ]
        p'   = subst (mkSubst (second EVar <$> xys)) p
        xys  = zipWith (\x i -> (x, S ("~A" ++ show i))) xs [0..] 
        xs   = delete v $ orderedFreeVars γ p

lookupSort t0 x γ = fromMaybe (errorstar msg) $ lookupSEnv x γ 
  where msg = "Unknown freeVar " ++ show x ++ " in specification " ++ show t0

orderedFreeVars γ = nub . filter (`memberSEnv` γ) . syms 

-- orderedFreeVars   :: Pred -> [Symbol]
-- orderedFreeVars p = nub $ everything (++) ([] `mkQ` f) p
--   where f (EVar x) = [x]
--         f _        = []


-- atoms' ps = traceShow ("atoms: ps = " ++ showPpr ps) $ atoms ps
atoms (PAnd ps) = concatMap atoms ps
atoms p         = [p]


