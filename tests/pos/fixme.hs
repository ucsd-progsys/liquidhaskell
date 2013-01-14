module ScopeCheck where

{-@ mmap      :: (a -> b) -> xs:[a] -> {v:[b] | (len v) = (len xs)} @-}
mmap _ []     = [] 
mmap f (x:xs) = (f x) : (mmap f xs)

