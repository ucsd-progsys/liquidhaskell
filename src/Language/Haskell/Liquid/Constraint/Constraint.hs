{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

-- TODO: what exactly is the purpose of this module? What do these functions do?

module Language.Haskell.Liquid.Constraint.Constraint (
  constraintToLogic
, addConstraints
) where

import Data.Maybe
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Constraint.Types
import Language.Haskell.Liquid.Constraint.Env
import Language.Fixpoint.Types

--------------------------------------------------------------------------------
addConstraints :: CGEnv -> [(Symbol, SpecType)] -> CGEnv
--------------------------------------------------------------------------------
addConstraints γ t = γ {lcs = mappend (t2c t) (lcs γ)}
  where
    t2c z          = LC [z]

--------------------------------------------------------------------------------
constraintToLogic :: CGEnv -> LConstraint -> Expr 
--------------------------------------------------------------------------------
constraintToLogic γ (LC ts) = pAnd (constraintToLogicOne γ  <$> ts)

-- RJ: The code below is atrocious. Please fix it!
constraintToLogicOne :: (Reftable r) => CGEnv -> [(Symbol, RRType r)] -> Expr
constraintToLogicOne γ binds -- env
  = pAnd [subConstraintToLogicOne
          (zip xs xts)
          (last xs,
          (last (fst <$> xts), r))
          | xts <- xss]
  where
   xts      = init binds
   (xs, ts) = unzip xts
   r        = snd $ last binds
   xss      = combinations ((\t -> [(x, t) | x <- bindsOfType t γ]) <$> ts)

subConstraintToLogicOne xts (x', (x, t)) = PImp (pAnd rs) r
  where
        (rs , su) = foldl go ([], []) xts
        ([r], _ ) = go ([], su) (x', (x, t))
        go (acc, su) (x', (x, t)) = let (Reft(v, p)) = toReft (fromMaybe mempty (stripRTypeBase t))
                                        su'          = (x', EVar x):(v, EVar x) : su
                                    in
                                     (subst (mkSubst su') p : acc, su')

combinations :: [[a]] -> [[a]]
combinations []           = [[]]
combinations ([]:_)       = []
combinations ((y:ys):yss) = [y:xs | xs <- combinations yss] ++ combinations (ys:yss)
