module Rec0 (clone, mk) where

{-@ data LL a = BXYZ { size  :: {v: Int | v > 0 }
                     , elems :: {v: [a] | (len v) = size }
                     }
  @-}

data LL a = BXYZ { size  :: Int
                 , elems :: [a]
                 }

{-@ mk :: a -> Int -> LL a @-}
mk x n = BXYZ n (clone x 0)

{-@ clone :: x:a -> n:Int -> {v:[a]| (len v) = n} @-}
clone :: a -> Int -> [a]
clone = undefined 
