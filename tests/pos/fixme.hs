{-@ LIQUID "--higherorder"   @-}
{-@ LIQUID "--totality"      @-}
{-@ LIQUID "--exactdc"       @-}

module MapReduce where

import Prelude hiding (map) -- , mconcat, split, take, drop, sum)
-- import Language.Haskell.Liquid.ProofCombinators

{-@ data List [llen] a = N | C {lhead :: a, ltail :: List a} @-}
data List a = N | C a (List a)

{-@ measure llen @-}
llen :: List a -> Int

{-@ llen :: List a -> Nat @-}
llen N        = 0
llen (C _ xs) = 1 + llen xs

{-@ reflect map @-}
{-@ map :: (a -> b) -> xs:List a -> List b / [llen xs] @-}
map :: (a -> b) -> List a -> List b
map _  N       = N
map f (C x xs) = f x `C` map f xs
