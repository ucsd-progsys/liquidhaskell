{-@ LIQUID "--expect-error-containing=Multiple definitions of Type Alias" @-}
module DuplicatedAliases () where

{-@ type Foo = {v:Bool | v == True} @-}

{-@ type Foo = {v:Bool | v == False} @-}
