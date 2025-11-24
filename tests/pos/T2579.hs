{-@ LIQUID "--reflection" @-}

module T2579 where 

{-@ qualif MyEqLen( v : [@(0)], x : int) { ((x = (len v)))  } @-}

{-@ type ListN a N = {v:[a] | len v = N} @-}

{-@ foldl' :: l:Nat
           -> (ListN a l -> ListN a l -> ListN a l)
           -> ListN a l -> [ListN a l] -> ListN a l @-}
foldl' :: Int -> ([a] -> [a] -> [a]) -> [a] -> [[a]] -> [a]
foldl' ins f acc xs = foldl f acc xs


-- foldl :: Foldable t => (b -> a -> b) -> b -> t a -> b