{-@ LIQUID "--expect-any-error" @-}
module TermReal where

{-@ search :: { hi : Int | 0 < hi } -> Int @-}
search :: Int -> Int
search hi = search (hi `div` 2)
