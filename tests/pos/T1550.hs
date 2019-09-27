{-@ LIQUID "--reflection" @-}

module Foo where 

{-@ reflect bar @-}
{-@ reflect foo @-}
{-@ reflect zoo @-}

bar, foo, zoo :: Int -> Int -> Int 

bar x y = x 
foo = bar 
zoo x = bar x 
