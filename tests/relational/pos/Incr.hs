module Incr where 

import Relational 

{-@ incr :: i:Int -> {o:Int | {i}1 < {i}2 => {o}1 < {o}2 } @-}
incr :: Int -> Int 
incr x = x `plus` one
