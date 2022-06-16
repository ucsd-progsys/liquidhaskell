{-@ LIQUID "--expect-any-error" @-}
module Total00 where

foo :: Int -> Int 
foo 0 = 0 
foo 1 = 1
