
module T1289a where

{-@ measure bintId @-}
bintId :: Int -> Int
bintId 0 = 0
bintId x = 1

{-@ zig :: n:Int -> { 0 <= bintId n && bintId n <= 1} @-}
zig :: Int -> ()  
zig 0 = () 
zig n = () 

