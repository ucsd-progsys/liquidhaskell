-- | test if basic opaque reflection is functioning

{-@ LIQUID "--reflection"      @-}

module OpaqueRefl01 (inc) where

c :: Int
c = 15

{-@ reflect inc @-}
inc :: Ord a => a -> a -> Int
inc a b = 9 + c