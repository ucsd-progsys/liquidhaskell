module Foo where

-- TODO: return a civilized error message about the line number with the
-- problematic predicate application, instead of just a groan about safeZip
-- failing.

{-@ predicate Rng Lo V Hi = (Lo <= V && V < Hi) @-}
{-@ type NNN a b  = {v:[(a, b)] | 0 <= 0} @-}

{-@ bog :: {v:Int | (Rng 0 10 11)} @-}
bog :: Int
bog = 5

{-@ foo :: NNN Int @-}
foo :: [(Int, Char)]
foo = [(1, 'c')]
