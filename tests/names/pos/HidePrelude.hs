
module HidePrelude where

import Prelude (Bool(..), Char, Maybe(..), Monad(..), Int,
                Num(..), Ord(..), ($), (&&),
                fromIntegral, otherwise)

{-@ incr :: Nat -> Nat @-}
incr :: Int -> Int 
incr x = x + 1
