module Infer00 () where

import Language.Haskell.Liquid.Prelude 

myId :: Int -> Int 
myId x = x 

prop n = liquidAssertB (n == m) 
  where 
     m = myId n 

