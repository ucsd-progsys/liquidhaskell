module Goo (
    module Moo 
  , plusTwo
 ) where

import Moo 

plusTwo :: Int -> Int
plusTwo = plusOne . plusOne

