{-@ LIQUID "--expect-error-containing=The type Test.Val was declared stratified but it is not an algebraic data type" @-}
module StratNotAdt where

{-@ stratified Val @-}
type Val = Int
