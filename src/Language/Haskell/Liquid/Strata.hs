{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}

module Language.Haskell.Liquid.Strata (
  SubStratum(..)
  ) where

import Control.Applicative      ((<$>))


import Language.Fixpoint.Types (Symbol)
import Language.Haskell.Liquid.Types hiding (Def, Loc)
import Language.Haskell.Liquid.Annotate (Annot(..))

class SubStratum a where
  subS  :: (Symbol, Stratum) -> a -> a
  subsS :: [(Symbol, Stratum)] -> a -> a

  subsS su x = foldr subS x su

instance SubStratum Stratum where
  subS (x, s) (SVar y) | x == y    = s
                       | otherwise = (SVar y)
  subS _      s        = s


instance (SubStratum a, SubStratum b) => SubStratum (a, b) where
  subS su (x, y) = (subS su x, subS su y)

instance (SubStratum a) => SubStratum [a] where
  subS su xs = subS su <$> xs

instance SubStratum Annot where
  subS su (Use t) = Use $ subS su t
  subS su (Def t) = Def $ subS su t
  subS su (RDf t) = RDf $ subS su t
  subS su (Loc s) = Loc s

instance SubStratum SpecType where
  subS su t = (\r -> r {ur_strata = subS su (ur_strata r)}) <$> t


