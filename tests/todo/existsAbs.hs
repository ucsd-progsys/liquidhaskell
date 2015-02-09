{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}



module Exists where

import Prelude hiding (exists)



{-
exists :: forall <p :: Bool -> Prop, q :: a -> Bool -> Prop, r :: a -> Prop>.
          (x:a -> Bool<q x>) -> [a<r>] -> Bool<p>

1. The result is True
    forall x::a, v :: Bool . r x => q x True  |- v = True => p v 
2. The result is False
    forall x::a, v :: Bool . r x /\ q x True => false  |- v = False => p v 

Eg:
1. If all the elements of the list satisfy q x True, then the result is true
exists isPos ([1, 2]  :: [Pos])        :: {v = True}
2. If all the elements of the list contradict q x True, then the result is false
exists isPos ([0, -1] :: [NonPos]) :: {v = False}
3. Otherwise, I have no info
exists isPos ([1, 0]  :: [Nat])        :: {true}

-}






{-@ exists :: forall <p :: Bool -> Prop, q :: a -> Bool -> Prop, r :: a -> Prop>.
                  {x::a, flag:: {v:Bool<q x> | Prop v}, y::a<r>, bb::{v:Bool | x = y} |- {v:Bool | Prop v <=> Prop flag } <: Bool<p>}
                  {x::a, flag:: {v:Bool<q x> | Prop v}, y::a<r>, bb::{v:Bool | x != y} |- {v:Bool | not (Prop v) <=> Prop flag } <: Bool<p>}
                  (x:a -> Bool<q x>) -> [a<r>] -> Bool<p>
  @-}


exists :: (a -> Bool) -> [a] -> Bool
exists f (x:xs)
  | f x       = True
  | otherwise = exists f xs 
exists _ []   = False
	
{-@ isPos :: x:Int -> {v:Bool | Prop v <=> x > 0} @-}
isPos :: Int -> Bool
isPos n = n > 0


{-@ isNeg :: x:Int -> {v:Bool | Prop v <=> x < 0} @-}
isNeg :: Int -> Bool
isNeg n = n < 0

prop0 :: Bool
{- prop0 :: {v:Bool | Prop v} @-}
prop0 = exists isPos [0, 1]
prop1 :: Bool
{- prop1 :: {v:Bool | not (Prop v)} @-}
prop1 = exists isPos [0, -1]

{-
-- | `positives` works by instantiating:
-- p := \v   -> 0 < v
-- q := \x v -> Prop v <=> 0 < x  (NV ??)


{- positives :: [Int] -> [{v:Int | v > 0}] @-}
positives xs = filter isPos xs


-- | `negatives` works by instantiating:
-- p := \v   -> 0 > v
-- q := \x v -> Prop v <=> x < 0

{- negatives :: [Int] -> [{v:Int | v < 0}] @-}
negatives xs = filter isNeg xs
-}