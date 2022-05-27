module ListReverse_LType (x, llen) where

import Language.Haskell.Liquid.Prelude        
import Prelude hiding (reverse)
data L a = N | C a (L a)

{-@ data L [llen] @-}

{-@ measure llen @-}
llen :: (L a) -> Int
{-@ llen :: L a -> Nat @-}
llen N        = 0
llen (C x xs) = 1 + (llen xs)

{-@ invariant {v: L a | (llen v) >= 0} @-}
reverse N xs = xs
reverse (C y ys) xs = reverse ys (C y xs)

x = reverse (C 1 (C 2 N))
