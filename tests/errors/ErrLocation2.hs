{-@ LIQUID "--expect-error-containing=ErrLocation2.hs:12:20" @-}

module ErrLocation2 where

{-@ inc :: Nat -> Nat @-}
inc :: Int -> Int 
inc x = x + 1

bar :: Int -> Int 
bar x 
 | x > 0    = inc (x - 1) 
 | otherwise = inc x 

