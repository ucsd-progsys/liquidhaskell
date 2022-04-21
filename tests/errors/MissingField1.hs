-- TODO-REBARE: LH _should_ (?) complain: "Unknown field `goober` in refined definition of `Foo`"

module MissingField1 where

data Foo = F Int 

{-@ data Foo = F { goober :: Int } @-}

