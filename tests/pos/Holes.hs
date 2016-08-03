module Holes (plus) where

{-@ foo :: x:_ -> y:{Int | y > 0} -> _ @-}
foo :: Int -> Int -> Int
foo x y = x

zero = foo 0 1


{-@ baz :: _ -> _ -> a @-}
baz :: a -> b -> b
baz x y = y

baz' = baz 1 2

data P a b = P a b

{-@ goo :: _ -> b -> _ @-}
goo :: P a b -> b -> a
goo p@(P a b) x = a

y = goo (P 1 1) 2


{-@ bar :: {v:[{v0:Int | v0 > 0}] | _ } -> Int @-}
bar :: [Int] -> Int
bar [x] = x

x =  bar [1]

{-@ plus :: x:_ -> y:_ -> {v:_ | v = x + y} @-}
plus :: Int -> Int -> Int 
plus x y = x + y


{-@ type UNat = {v:_ | v >= 0} @-}

{-@ zoo :: UNat @-}
zoo = 1
