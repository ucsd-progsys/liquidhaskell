module GList00Lib where

{-@ die :: {v: () | false} -> a @-}
die :: () -> a
die = undefined 

{-@ safeHead :: {v:[a] | llen v > 0} -> a @-} 
safeHead :: [a] -> a 
safeHead (x:_) = x 
safeHead []    = die () 

{-@ measure llen @-}
{-@ llen :: [a] -> Nat @-}
llen :: [a] -> Int
llen []     = 0 
llen (x:xs) = 1 + llen xs 
