{-# LANGUAGE MagicHash #-}
-- | Tests that LH can reason with literals using the IS data constructor
module T2237 () where

import Language.Haskell.Liquid.Prelude (liquidError, liquidAssertB)
import qualified GHC.Num.Integer

data Foo a = F a

{-@ flibInt :: (Num a, Ord a) => a -> Bool @-}
flibInt x     = prop1 x (F (x + fromInteger (GHC.Num.Integer.IS 1#)))
prop1 x (F y) = liquidAssertB (x < y)
