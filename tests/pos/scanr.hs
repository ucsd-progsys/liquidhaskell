module Goo () where

{-@ assert scanrr  :: forall a b. (a -> b -> b) -> b -> xs:[a] -> {v: [b] | len(v) = 1 + len(xs) } @-}
scanrr             :: (a -> b -> b) -> b -> [a] -> [b]
scanrr _ q0 []     =  [q0]
scanrr f q0 (x:xs) =  f x q : qs
                      where qs@(q:_) = scanrr f q0 xs 
