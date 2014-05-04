module Invariant where

data F a = F {fx :: a, fy :: a, fzz :: a} 
         | G {fx :: a, fy :: a}

{-@ data F a = F {fx :: a, fy :: a, fz :: a}
             | G {fx :: a, fy :: a} 
  @-}

{-@ invariant {v : F a | (fy v) = (fx v) } @-}

-- F :: x:a -> y:a -> z:a -> { prove this } -> F a


{-@ foo :: x:a -> a-> {v : F a | (fx v) = x} @-}
foo :: a -> a -> F a
foo x y = F x y x

