module State00 () where

type State  = Int
data ST a b = Superb (b -> (a, b)) 

{-@ fresh :: ST {v:Int | v >= 0} {v:Int | v >= 0} @-}
fresh :: ST Int Int
fresh = Superb (\n -> (n, n+1))


