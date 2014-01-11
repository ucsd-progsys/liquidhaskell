{-# LANGUAGE ScopedTypeVariables #-}

module List () where

{-@ Decrease go 3 4 5 @-}
{-@ Decrease perms 4 5 6 @-}

{-@ foo :: xs:[a] -> ys:[a] -> {v:Int| v = (len xs)- (len ys)} -> Int @-}
foo :: [a] -> [a] -> Int -> Int
foo = undefined

permutations         :: [a] -> [[a]]
permutations xs     =  go xs xs (length xs) (length xs) 1
  where
    go xs0 xs (d2 :: Int) d1 (d3::Int) = xs : perms xs0 xs [] d2 d1 0
    perms _ []     _  _ _ _ = []
    perms xs0 (t:ts) is (d2 :: Int) (d1::Int) (d3 :: Int) = (perms ts xs0 (t:is) d2 (length ts) d3) ++ (go xs0 is (length xs0 - length is) d1 1)

-- permutations         :: [a] -> [[a]]
-- permutations xs     =  go xs xs (length xs) (0::Int) 1
--   where
--     go xs0 xs d1 (d2::Int) (d3::Int) = xs : perms xs0 xs [] d1 0 0
--     perms _ []     _  _ _ _ = []
--     perms xs0 (t:ts) is (d1::Int) (d2 :: Int) (d3 :: Int) = (perms ts xs0 (t:is) (length ts) 0 d3) ++ (go xs0 is (length is) 0 1)
-- 
-- 
