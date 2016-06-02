module EliminateCuts (bar) where

{-@ bar :: n:{Int | n > 0} -> {v:Int | v = n + 4 } @-}
bar :: Int -> Int 
bar n0 = let 
            n1 = if (n0 == 0) then 0 else 1 + n0
            n2 = if (n1 == 0) then 0 else 1 + n1
            n3 = if (n2 == 0) then 0 else 1 + n2
            n4 = if (n3 == 0) then 0 else 1 + n3
         in 
            n4
