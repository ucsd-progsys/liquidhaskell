-- Tests that the "class measure" `len` works properly.

module Len00 where

-- safeHd :: [a] -> a 

bloop :: Int
bloop = safeHd [1,2]

{-@ safeHd :: { v : [a] | 0 < len v } -> a @-}
safeHd (x:_) = x 
safeHd _     = die () 

{-@ die :: {v:_ | false} -> a @-}
die :: () -> a 
die _ = undefined 
