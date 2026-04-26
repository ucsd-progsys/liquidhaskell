{- | Test that abstract refinement predicates on parenthesized types
     are correctly propagated. (Pair Int Int)<p> should behave the same
     as Pair<p> Int Int.
-}
module ParenAbsRef where

{-@ data Pair a b <p :: a -> b -> Bool> = Pair { pFst :: a, pSnd :: b<p pFst> } @-}
data Pair a b = Pair a b

-- Parenthesized form: the predicate applies to the Pair type constructor
{-@ type OrdPair = (Pair Int Int) <{\x y -> x <= y}> @-}

{-@ mkGood :: OrdPair @-}
mkGood :: Pair Int Int
mkGood = Pair 3 5
