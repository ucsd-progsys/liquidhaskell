{-@ LIQUID "--expect-error-containing=ErrLocation.hs:10:13" @-}

module ErrLocation where

{-@ inc :: Nat -> Nat @-}
inc :: Int -> Int 
inc x = x + 1

bar :: Int -> Int 
bar x = inc (x - 1)

