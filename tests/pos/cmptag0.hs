module Test () where

{-@ type OList a = [a]<{\fld v -> (v >= fld)}> @-}

{-@ foo :: (Ord a) => z:a -> OList a -> [{v:a | z <= v}] @-}
foo y xs = bar y xs

bar :: (Ord a) => a -> [a] -> [a]
bar y []     = []
bar y z@(x:xs) = case compare y x of 
                   EQ -> xs
                   GT -> bar y xs
                   LT -> x:xs
