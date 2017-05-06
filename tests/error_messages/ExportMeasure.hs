module ExportMeasure () where

data LL a = N | C a (LL a)

{-@ invariant {v:LL a | (llen v) >= 0} @-}

{-@ measure llen @-}
llen :: (LL a) -> Int 
llen(N)      = 0
llen(C x xs) = 1 + (llen xs)

{-@ lmap :: (a -> b) -> xs:(L a) -> {v: L b | llen v = llen xs } @-} 
lmap f N = N
lmap f (C x xs) = C (f x) (lmap f xs)
