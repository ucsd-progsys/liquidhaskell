-- | issue #765 we get complete gibberish for inferred types
-- * nothing for 'gunk'
-- * {v = 1} for `z`

module Bar where

{-@ bar :: Nat -> Nat @-}
bar :: Int -> Int 
bar z = let gunk = z + 1 
        in gunk
