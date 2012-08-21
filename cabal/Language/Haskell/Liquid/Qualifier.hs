{-# LANGUAGE DeriveDataTypeable #-}
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
import Data.List                (nub, delete)
import Data.Maybe               (fromMaybe)
import qualified Data.Set as S
import Data.Bifunctor           (second) 
import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Data


data Qualifier = Q { name   :: String
                   , params :: [(Symbol, Sort)]
                   , pred   :: Pred
                   } deriving (Eq, Ord, Data, Typeable)

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

specificationQualifiers         :: GhcInfo -> [Qualifier] 
specificationQualifiers info    = [ q | (x, t) <- tySigs $ spec info
                                      , x `S.member` xs
                                      , q      <- refTypeQuals $ ureft <$> t
                                  ] where xs = S.fromList $ defVars info 

refTypeQuals                    :: RefType -> [Qualifier] 
refTypeQuals t0 = go emptySEnv t0
  where go γ t@(RVar _ _)         = refTopQuals t0 γ t     
        go γ (RAll α t)           = go γ t 
        go γ (RFun (RB x) t t' _) = (go γ t) ++ (go (insertSEnv x (rTypeSort t) γ) t')
        go γ t@(RApp _ ts _ _)    = (refTopQuals t0 γ t) ++ concatMap (go γ) ts 
        go γ _                    = []

refTopQuals t0 γ t 
  = [ mkQual t0 γ v so p | let (RR so (Reft (v, ras))) = refTypeSortedReft t 
                         , RConc p                    <- ras                 ]

mkQual t0 γ v so p = Q "Auto" ((v, so) : yts) p'
  where yts  = [(y, lookupSort t0 x γ) | (x, y) <- xys ]
        p'   = subst (mkSubst (second EVar <$> xys)) p
        xys  = zipWith (\x i -> (x, S ("~A" ++ show i))) xs [0..] 
        xs   = delete v $ orderedFreeVars p

lookupSort t0 x γ = fromMaybe (errorstar msg) $ lookupSEnv x γ 
  where msg = "Unknown freeVar " ++ show x ++ "In specification " ++ show t0

orderedFreeVars   :: Pred -> [Symbol]
orderedFreeVars p = nub $ everything (++) ([] `mkQ` f) p
  where f (EVar x) = [x]
        f _        = []




