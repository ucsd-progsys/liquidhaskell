module PruneHO where

-- test that you suitably deal with _pruned_ higher order binders.
-- CURRENTLY, this works with --reflection because we don't nuke 
-- the TUPLE CONTAINING `incr` from the env; note that `snd p` 
-- introduces the "malformed" refinement `v = snd p` but `p` is 
-- HIGHER order and so is nuked, causing the problem.

incr :: Int -> Int 
incr x = x + 1 

{-@ foo :: Nat @-}
foo :: Int 
foo = snd (incr, 12)
