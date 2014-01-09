module Reverse () where

import Language.Haskell.Liquid.Prelude        
import Prelude hiding (reverse)
data L a = N | C a (L a)



{-@ data L [llen] @-}

{-@ measure llen :: (L a) -> Int
    llen(N)      = 0
    llen(C x xs) = 1 + (llen xs)
  @-}

{-@ invariant {v: L a | (llen v) >= 0} @-}

{-@ reverse :: xs: L a -> ys : L a -> L a / [(llen xs)] @-}
reverse :: L a -> L a -> L a
reverse xs N = xs
reverse xs (C y ys) = reverse (C y xs) ys
