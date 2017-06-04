module DPairs where


{-@ incrPair :: Int -> (x::Int, {v:Int | x <= v}) @-}
incrPair :: Int -> (Int, Int)
incrPair i = (i, i+1)


{-@ assertDep :: (Int, Int)<\x -> {v:Int | x <= v}> -> {b:Bool | b} @-}
assertDep :: (Int, Int) -> Bool 
assertDep (x, y) = x <= y



{-@ goalDep :: (x::Int, {v:Int | x <= v}) -> {b:Bool | b} @-}
goalDep :: (Int, Int) -> Bool 
goalDep (x, y) = x <= y
