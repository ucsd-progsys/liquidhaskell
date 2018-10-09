-- test that the name `length` is actually resolved to the local definition,
-- not the thing imported from Prelude! 

module HideName00 where

import Prelude hiding (length) 

{-@ measure length @-}
length :: Bool -> Int 
length True  = 1 
length False = 0 
