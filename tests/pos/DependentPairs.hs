module DPairs where


{-@ incrPair :: (x::Int, {v:Int | x <= v}) @-}
incrPair :: (Int, Int)
incrPair = (2, 3)


{-@ assertDep :: (Int, Int)<\x -> {v:Int | x <= v}> -> {b:Bool | b} @-}
assertDep :: (Int, Int) -> Bool 
assertDep (x, y) = x <= y



{-@ goalDep :: (x::Int, {v:Int | x <= v}) -> {b:Bool | b} @-}
goalDep :: (Int, Int) -> Bool 
goalDep (x, y) = x <= y
