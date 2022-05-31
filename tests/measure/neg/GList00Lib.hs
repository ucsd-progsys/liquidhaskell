{-@ LIQUID "--expect-any-error" @-}
module GList00Lib where

{-@ die :: {v: () | false} -> a @-}
die :: () -> a
die = undefined 

{-@ safeHead :: {v:[a] | 0 <= llen v} -> a @-} 
safeHead :: [a] -> a 
safeHead (x:_) = x 
safeHead []    = die () 

{-@ measure llen @-}
{-@ llen :: [a] -> Nat @-}
llen :: [a] -> Int
llen []     = 0 
llen (x:xs) = 1 + llen xs 
