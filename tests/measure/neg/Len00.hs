{-@ LIQUID "--expect-any-error" @-}
-- Tests that the "class measure" `len` works properly.

module Len00 where

{-@ die :: {v:_ | false} -> a @-}
die :: () -> a 
die _ = undefined 

{-@ safeHd :: { v : [a] | 0 < len v } -> a @-}
safeHd (x:_) = x 
safeHd _     = die () 

bloop :: Int
bloop = safeHd []

