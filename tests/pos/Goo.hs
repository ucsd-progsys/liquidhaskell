module Goo (
    module Moo 
  , plusTwo
 ) where

import Moo 

{-@ plusTwo :: x:Int -> {v:Int | v = 43} @-}
plusTwo :: Int -> Int
plusTwo = plusOne 

