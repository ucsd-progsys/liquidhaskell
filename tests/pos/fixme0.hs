module ListSort  where

{-@ type GN N = {v:a | v >= N}  @-}

{-@ mergesort :: x:a -> GN x @-}
mergesort :: a -> a
mergesort x  = x

