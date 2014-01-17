module Permutation () where

{-@ permutations :: ts:[a] -> [[a]] / [(len ts), 1, 0] @-}
permutations            :: [a] -> [[a]]
permutations xs0        =  xs0 : perms xs0 []

{-@ perms :: ts:[a] -> is:[a] -> [[a]] / [((len ts)+(len is)), 0, (len ts)] @-}
perms :: [a] -> [a] -> [[a]]
perms []     _  = []
perms (t:ts) is = foldr interleave (perms ts (t:is)) (permutations is)
      where interleave    xs     r = let (_,zs) = interleave' id xs r in zs
            interleave' _ []     r = (ts, r)
            interleave' f (y:ys) r = let (us,zs) = interleave' (f . (y:)) ys r
                                     in  (y:us, f (t:y:us) : zs)


