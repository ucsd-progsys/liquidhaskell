module Language.Haskell.Liquid.Simplify (simplifyBounds) where

import Language.Haskell.Liquid.Types
import Language.Fixpoint.Types
import Language.Fixpoint.Visitor
-- import Control.Applicative                 ((<$>))
import Data.Monoid

simplifyBounds :: SpecType -> SpecType
simplifyBounds = fmap go
  where
    go x       = x { ur_reft = go' $ ur_reft x }
    -- OLD go' (Reft (v, rs)) = Reft(v, filter (not . isBoundLike) rs)
    go' (Reft (v, Refa p)) = Reft(v, Refa $ dropBoundLike p)

dropBoundLike :: Pred -> Pred
dropBoundLike p
  | isKvar p          = p
  | isBoundLikePred p = mempty
  | otherwise         = p
  where
    isKvar            = not . null . kvars

isBoundLikePred :: Pred -> Bool
isBoundLikePred (PAnd ps) = simplifyLen <= length [p | p <- ps, isImp p ]
isBoundLikePred _         = False

isImp :: Pred -> Bool
isImp (PImp _ _) = True
isImp _          = False

-- OLD isBoundLike (RConc pred)  = isBoundLikePred pred
-- OLD isBoundLike (RKvar _ _)   = False


-- OLD moreThan 0 _            = True
-- OLD moreThan _ []           = False
-- OLD moreThan i (True  : xs) = moreThan (i-1) xs
-- OLD moreThan i (False : xs) = moreThan i xs

simplifyLen :: Int
simplifyLen = 5

