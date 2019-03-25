module Relational where 

{-@ measure relational :: a -> int -> a @-}


{-@ assume plus :: x:Int -> y:Int -> {z:Int | z == x + y && {z}1 == {x}1 + {y}1 && {z}2 == {x}2 + {y}2 } @-}
plus :: Int -> Int -> Int 
plus = (+)

{-@ assume minus :: x:Int -> y:Int -> {z:Int | z == x - y && {z}1 == {x}1 - {y}1 && {z}2 == {x}2 - {y}2 } @-}
minus :: Int -> Int -> Int 
minus = (-)

{-@ assume one :: {v:Int | v == 1 && {v}1 == 1 && {v}2 == 1 } @-}
one :: Int
one = 1 


{-@ assume zero :: {v:Int | v == 0 && {v}1 == 0 && {v}2 == 0 } @-}
zero :: Int
zero = 0