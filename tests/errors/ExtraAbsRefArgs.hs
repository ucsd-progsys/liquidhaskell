{-@ LIQUID "--expect-error-containing=does not accept abstract refinement arguments" @-}

-- Test for issue #2603: abstract refinement predicate applied to a type
-- constructor that doesn't declare any abstract refinement parameters.
-- Without parentheses around (Pair ...), the parser attaches <{...}> to Int
-- which has no abstract refinement parameters.

module ExtraAbsRefArgs where

{-@ data Pair a b <p :: a -> b -> Bool> = MkPair { pfst :: a, psnd :: b<p pfst> } @-}
data Pair a b = MkPair { pfst :: a, psnd :: b }

-- The <{...}> gets attached to Int, not to Pair
{-@ foo :: Pair Int Int <{\x y -> x <= y}> @-}
foo :: Pair Int Int
foo = MkPair 1 2
