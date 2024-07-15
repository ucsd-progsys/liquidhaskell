-- | Duplicate specifications
{-@ LIQUID "--expect-error-containing=Multiple specifications for `DuplicateSpecs.incr`" @-}

module DuplicateSpecs where

{-@ incr :: x:_ -> {v:_ | v = x + 1} @-}
incr :: Int -> Int 
incr x = x + 1

{-@ incr :: x:_ -> {v:_ | v = x - 1} @-}