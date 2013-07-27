module Foo where

-- TODO: Expressions inside applications of type and predicate aliases.

{-@ type IntRng Lo Hi = {v:Int | (Lo <= v && v < hi)} @-}

{-@ bog :: (IntRng 0 10) @-}
bog :: Int
bog = 5
