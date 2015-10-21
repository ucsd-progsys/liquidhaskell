module ListQual (boo) where

{-@ qualif BadAppend(v:[a], xs:[a], ys:[a]): len v = len xs + len ys @-}

append [] ys     = ys
append (x:xs) ys = x : append xs ys

{-@ boo :: {v:[Int] | len v = 2} @-}
boo :: [Int]
boo = append [1] [2]
