module Tx () where

{-@ assert compre :: xs:[a] -> {v:[(a,a)] | len(v) = len(xs) } @-}
compre xs = [(x,x) | x <- xs]

{-@ assert transpose :: n: Int -> [{v:[a] | len(v) = n}] -> {v: [[a]] | len(v) > n} @-}
transpose               :: Int -> [[a]] -> [[a]]
transpose 0 _              = []
transpose n ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (n-1) (xs : [ t | (_:t) <- xss]) 
-- transpose []             = []
-- transpose ([]   : xss)   = transpose xss


