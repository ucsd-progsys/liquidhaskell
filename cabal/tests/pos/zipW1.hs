module T where

{-@ assert foo :: (a -> b -> c) -> xs : [a] -> ys:{v:[b] | len(v) = len(xs)} -> {v : [c] | len(v) = len(xs)} @-}
foo = zipWith

