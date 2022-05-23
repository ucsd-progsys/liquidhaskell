-- Tests that the "class measure" `len` works properly.

module Len01 where

-- safeHd :: [a] -> a 

bloop :: Char 
bloop = safeHd "cat"

{-@ safeHd :: { v : [a] | 0 < len v } -> a @-}
safeHd (x:_) = x 
safeHd _     = die "safeHd"

{-@ die :: {v:_ | false} -> a @-}
die :: String -> a 
die = error 
