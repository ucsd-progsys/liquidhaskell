module Foo where

-- TODO: return a civilized error message about the line number with the
-- problematic predicate application, instead of just a groan about safeZip
-- failing.

{-@ predicate Rng Lo V Hi = (Lo <= V && V < Hi) @-}

{-@ bog :: {v:Int | (Rng 0 10)} @-}
bog :: Int
bog = 5
