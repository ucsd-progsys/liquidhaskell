{-@ LIQUID "--reflection" @-}

{-@ reflect flob @-}
flob :: String -> Int 
flob x = if x == "cat" then 1 else 2

{-@ check1:: () -> {v:Int | v = flob "cow" } @-}
check1 :: () -> Int
check1() = flob "cow"

{-@ check2:: () -> {v:Int | pcow v } @-}
check2:: () -> Int
check2() = flob "cow"

{-@ inline pcow @-}
pcow :: Int -> Bool 
pcow v = v == flob "cow"
