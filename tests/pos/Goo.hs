module Goo (
    module Moo 
  , plusTwo
 ) where

import Moo 

{-@ plusTwo :: x:Int -> {v:Int | v = x + 2} @-}
plusTwo :: Int -> Int
plusTwo = plusOne . plusOne

