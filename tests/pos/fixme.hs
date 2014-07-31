module Test0 () where

{-@ single :: a -> {v:[a] | len v > 0} @-}
single x = [x] 
