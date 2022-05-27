module LibRedBlue where

import LibRed 
import qualified LibBlue as Blue 

{-@ foo :: Thing -> Nat @-}
foo :: Thing -> Int  
foo _ = 10 
