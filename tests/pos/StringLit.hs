module StringLit where

{-@ foo :: {v:String | len v = 3} @-}
foo = "foo"
