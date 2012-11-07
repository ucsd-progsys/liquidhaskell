module Rec0 (clone, mk) where

{-@ data LL a = B { size  :: {v: Int | v > 0 }
                  , elems :: {v: a   | (len a) = size }
                  }
  @-}

data LL a = B { size  :: Int
              , elems :: [a]
              }

mkLL x n = B n (clone x 5)

{-@ clone :: x:a -> n:Int -> {v:[a]| (len v) = n} @-}
clone :: a -> Int -> [a]
clone = error "FOO"
