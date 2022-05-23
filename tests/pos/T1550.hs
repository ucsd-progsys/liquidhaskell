{-@ LIQUID "--reflection" @-}

module T1550 where

import Language.Haskell.Liquid.Equational

{-@ reflect bar @-}
{-@ reflect foo @-}
{-@ reflect zoo @-}

bar, foo, zoo :: Int -> Int -> Int 

bar x y = x 
foo = bar 
zoo x = bar x 


{-@ fooId :: x:Int -> y:Int -> { foo x y = x } @-}
fooId :: Int -> Int  -> Proof 
fooId x y = foo x y ==. bar x y ==. x *** QED 


{-@ barId :: x:Int -> y:Int -> { bar x y = x } @-}
barId :: Int -> Int  -> Proof 
barId x y = bar x y ==. x *** QED 

{-@ zooId :: x:Int -> y:Int -> { bar x y = x } @-}
zooId :: Int -> Int  -> Proof 
zooId x y = zoo x y ==. bar x y ==. x *** QED 
