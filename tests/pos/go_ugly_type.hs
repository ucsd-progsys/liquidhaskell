module ID () where

{-@ qualif Poo(v:a, x:a, y:a): (len v) = (len x) + (len y) @-}

{-@ Decrease go 2 @-}

{-@ rev :: xs:[a] -> {v: [a] | (len v) = (len xs)} @-}
rev = go [] 
  where 
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs
