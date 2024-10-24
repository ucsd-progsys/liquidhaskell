{-@ LIQUID "--expect-error-containing=Multiple definitions of Type Alias" @-}
module DuplicatedAliases where

{-@ type Nat = {v:Int | v >= 0} @-}
