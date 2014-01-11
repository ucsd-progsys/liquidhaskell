module Test () where

{-@ sz :: {v:[a]|((len v) = 1)} -> a @-}
-- sz (x:xs) = sz xs
sz [x]    = x

{-@ poo :: [a] -> a @-}
poo (x:xs) = poo xs
poo [x]    = x
poo _      = error "poo"
