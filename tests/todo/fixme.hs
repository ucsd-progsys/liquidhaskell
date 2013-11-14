{-# LANGUAGE ScopedTypeVariables #-}

module List where

{-@ Decrease go 1 2 @-}
{-@ Decrease perms 1 2 @-}
-- THIS IS SAFE DUE TO PRONNING.....

permutations         :: [a] -> [[a]]
permutations xs     =  go xs (length xs)
  where
    go xs (d::Int)  = xs : perms xs []
    perms []     _  = []
    perms (t:ts) is = (perms ts (t:is)) ++ (go is xxxxx)
          where xxxxx = length is

