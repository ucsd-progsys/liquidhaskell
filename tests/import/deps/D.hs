module D where

import qualified C

{-@ gloob :: x:Nat -> Nat @-}
gloob :: Int -> Int 
gloob x = C.quux x x x

