module Rec0 (clone, mk) where

{-@ data LL a = BXYZ { size  :: {v: Int | v > 0 }
                     , elems :: {v: [a] | (len v) = size }
                     }
  @-}

data LL a = BXYZ { size  :: Int
                 , elems :: [a]
                 }

{-@ mk :: a -> Int -> LL a @-}
mk x n | n > 0     = BXYZ n (clone x n) 
       | otherwise = BXYZ 1 [x]


{-@ clone :: x:a -> n:Int -> {v:[a]| (len v) = n} @-}
clone :: a -> Int -> [a]
clone = error "FOO"
