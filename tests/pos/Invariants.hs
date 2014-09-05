module Invariant where

import Language.Haskell.Liquid.Prelude

data F a = F {fx :: a, fy :: a, fzz :: a} 
         | G {fx :: a, fy :: a}

{-@ data F a = F {fx :: a, fy :: a, fz :: a}
             | G {fx :: a, fy :: a} 
  @-}

{-@ using (F a) as {v : F a | (fy v) = (fx v) } @-}

-- F :: x:a -> y:a -> z:a -> { prove this } -> F a


{-@ foo :: x:a -> a -> {v : F a | x = fx v} @-}
foo :: a -> a -> F a
foo x y = F x x y

bar (F x y z) = liquidAssert (x == y)
