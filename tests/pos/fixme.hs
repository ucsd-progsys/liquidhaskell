module Test where

{-@ type OList a = [a]<{v: a | (v >= fld)}> @-}

{-@ bar :: (Ord a) => z:a -> OList a -> [{v:a | z <= v}] @-}
bar :: (Ord a) => a -> [a] -> [a]
bar y z@(x:xs) = case compare y x of 
                   LT -> x:xs
