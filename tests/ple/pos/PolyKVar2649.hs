{-@ LIQUID "--ple" @-}
module PolyKVar2649 where

-- | A polymorphic helper with kvar-inferred refinements.
-- The spec says: given input satisfying some kvar, produce output satisfying some kvar.
-- The implementation is the identity, so the output equals the input.
{-@ go :: {acc:[a] | _} -> {v:[a] | _ } @-}
go :: [a] -> [a]
go xs = xs

-- | A wrapper that calls `go` polymorphically.
-- The kvars in `go` are instantiated with a different type variable context,
-- exercising the polymorphic kvar mechanism (issue #2649).
{-@ wrap :: xs:[a] -> {v:[a] | len v >= 0 } @-}
wrap :: [a] -> [a]
wrap xs = go xs
