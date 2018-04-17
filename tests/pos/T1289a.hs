
{-@ measure bintId @-}
bintId :: Int -> Int
bintId 0 = 0
bintId x = x

{-@ zig :: n:Int -> {v:Int | v = bintId n} @-}
zig :: Int -> Int 
zig 0 = 0 
zig 1 = 1 
zig n = n 

