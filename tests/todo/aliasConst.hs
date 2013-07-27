module Foo where

-- TODO: Expressions inside applications of type and predicate aliases.

{-@ predicate Rng Lo V Hi = (Lo <= V && V < Hi) @-}

{-@ bog :: {v:Int | (Rng 0 v 10)} @-}
bog :: Int
bog = 5
