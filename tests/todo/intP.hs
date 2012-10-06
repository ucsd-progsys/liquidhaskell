module Qoo where

{-@ intid :: forall <r :: y0: Int -> Bool>. i: Int<r> -> Int<r> @-}
intid :: Int -> Int
intid i = i

