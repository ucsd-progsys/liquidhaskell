module Test where

{-@ bar :: (a, [b]) -> b @-}
bar (_, [x]) = x



