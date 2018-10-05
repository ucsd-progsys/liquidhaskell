module LooLib ( module LooLibLib , plusTwo ) where

import LooLibLib 

{-@ plusTwo :: x:Int -> {v:Int | v = x + 2} @-}
plusTwo :: Int -> Int
plusTwo = plusOne . plusOne

