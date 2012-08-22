module Test where

{- bar :: x:Maybe a -> {v:Bool | ((isJust(x)) => (fromJust(x) = v)) } @-}
foo :: Maybe Int -> Int
foo (Just x)  = x 
foo (Nothing) = 0

{-@ bar :: x:Maybe a -> {v:Bool | ((isJust(x)) <=> (? v)) } @-}
bar (Just x)  = True 
bar (Nothing) = False

