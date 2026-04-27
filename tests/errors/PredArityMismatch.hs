{-@ LIQUID "--expect-error-containing=Malformed predicate application" @-}

-- Test for arity mismatch: predicate expects 2 arguments (a -> b -> Bool)
-- but is given a 3-argument lambda.

module PredArityMismatch where

{-@ data Pair a b <p :: a -> b -> Bool> = MkPair { pfst :: a, psnd :: b<p pfst> } @-}
data Pair a b = MkPair { pfst :: a, psnd :: b }

{-@ foo :: Pair <{\x y z -> x <= y}> Int Int @-}
foo :: Pair Int Int
foo = MkPair 1 2
