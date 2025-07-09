{-@ LIQUID "--expect-error-containing=Ambiguous specification symbol" @-}
module DuplicatedAliases where

{-@ type Nat = {v:Int | v >= 0} @-}

{-@ test :: Nat @-}
test :: Int
test = 0
