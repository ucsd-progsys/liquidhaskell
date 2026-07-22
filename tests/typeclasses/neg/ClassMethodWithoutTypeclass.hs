{-@ LIQUID "--expect-error-containing=This is a class method, but typeclass support is disabled." @-}
module ClassMethodWithoutTypeclass where

import Prelude (Int, Enum(succ))

{-@ succId :: x:Int -> {v:Int | succ x == succ x} @-}
succId :: Int -> Int
succId x = x
