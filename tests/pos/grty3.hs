module Test where

{-@ bar :: (a, {v:[b]|((len v) = 1)}) -> b @-}
bar (_, [x]) = x



