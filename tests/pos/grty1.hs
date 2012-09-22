module Test where

{-@ sz :: [a] -> a @-}
-- sz (x:xs) = sz xs
sz [x]    = x

{-@ poo :: [a] -> a @-}
poo (x:xs) = poo xs
poo [x]    = x
