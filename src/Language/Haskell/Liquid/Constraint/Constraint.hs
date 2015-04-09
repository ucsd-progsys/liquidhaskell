{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Constraint.Constraint  where

import Data.Monoid
import Data.Maybe
import Control.Applicative 

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Constraint.Types

import Language.Fixpoint.Types

instance Monoid LConstraint where
	mempty  = LC []
	mappend (LC cs1) (LC cs2) = LC (cs1 ++ cs2) 

typeToConstraint t = LC [t]


addConstraints t γ = γ {lcs = mappend (typeToConstraint t) (lcs γ)}

constraintToLogic γ (LC ts) = pAnd (constraintToLogicOne γ  <$> ts)

constraintToLogicOne γ env
  =  pAnd [subConstraintToLogicOne 
            (zip xs xts) 
            (last xs, 
            (last $ (fst <$> xts), r))  
          | xts <- xss]
  where 
   xts      = init env 
   (xs, ts) = unzip xts 
   r        = snd $ last env
   xss      = combinations ((\t -> [(x, t) | x <- grapBindsWithType t γ]) <$> ts)

subConstraintToLogicOne xts (x', (x, t)) = PImp (pAnd rs) r
  where
  	(rs , su) = foldl go ([], []) xts
  	([r], _ ) = go ([], su) (x', (x, t))
  	go (acc, su) (x', (x, t)) = let (Reft(v, rr)) = toReft (fromMaybe mempty (stripRTypeBase t)) in
                                let su' = (x', EVar x):(v, EVar x):su in
                                (subst (mkSubst su') (pAnd [p | RConc p <- rr]):acc, su')



combinations :: [[a]] -> [[a]]
combinations []           = [[]]
combinations ([]:_)       = []
combinations ((y:ys):yss) = [y:xs | xs <- combinations yss] ++ combinations (ys:yss)

