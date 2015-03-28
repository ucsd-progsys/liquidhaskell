module Language.Haskell.Liquid.Simplify (simplifyBounds) where

import Language.Haskell.Liquid.Types

import Language.Fixpoint.Types

import Control.Applicative                 ((<$>))

simplifyLen = 5

simplifyBounds :: SpecType -> SpecType
simplifyBounds = fmap go
  where
        go x = x{ur_reft = go' $ ur_reft x}

        go' (Reft (v, rs)) = Reft(v, filter (not . isBoundLike) rs)

        isBoundLike (RConc pred) = isBoundLikePred pred
        isBoundLike (RKvar _ _)  = False

        isBoundLikePred (PAnd ps)
          = moreThan simplifyLen (isImp <$> ps)
        isBoundLikePred _ = False

        isImp (PImp _ _) = True
        isImp _          = False

        moreThan 0 _          = True
        moreThan _ []         = False
        moreThan i (True:xs)  = moreThan (i-1) xs
        moreThan i (False:xs) = moreThan i xs
