{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

-- TODO: what exactly is the purpose of this module? What do these functions do?

module Language.Haskell.Liquid.Constraint.Constraint (
  constraintToLogic
, addConstraints
) where

import Prelude hiding (error)
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
constraintToLogic :: REnv -> LConstraint -> Expr
--------------------------------------------------------------------------------
constraintToLogic γ (LC ts) = pAnd (constraintToLogicOne γ <$> ts)

-- RJ: The code below is atrocious. Please fix it!
constraintToLogicOne :: (Reftable r) => REnv -> [(Symbol, RRType r)] -> Expr
constraintToLogicOne γ binds
  = pAnd [subConstraintToLogicOne
          (zip xs xts)
          (last xs,
          (last (fst <$> xts), r))
          | xts <- xss]
  where
   xts      = init binds
   (xs, ts) = unzip xts
   r        = snd $ last binds
   xss      = combinations ((\t -> [(x, t) | x <- localBindsOfType t γ]) <$> ts)

subConstraintToLogicOne :: (Foldable t, Reftable r, Reftable r1)
                        => t (Symbol, (Symbol, RType t1 t2 r))
                        -> (Symbol, (Symbol, RType t3 t4 r1)) -> Expr
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
