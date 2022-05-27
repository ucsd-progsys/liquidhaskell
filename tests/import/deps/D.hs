module D where

import qualified CLib

{-@ gloob :: x:Nat -> Nat @-}
gloob :: Int -> Int 
gloob x = C.quux x x x

