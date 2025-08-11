-- | Predicate aliases are stored alongside lifted @inline@ and @define@ annotations
-- as logical expression aliases. Several different @predicates@ are defined and
-- used to account for the use different logic constructs.
module ExprAliases (isNegative, successor, SetS, addToEmptySetS, emptySetS) where

import Data.Set (Set)
import qualified Data.Set as Set

{-@ predicate InSomeRange X = X >= 1  && X <= 10@-}

{-@ predicate Divides X Y = (Y mod X) = 0 @-}

{-@ predicate Negative X = X < 0 @-}

{-@ predicate LessThanSomeNum X =  X < 3 @-}

-- Both @define@ and @inline@ lift a Haskell function to the logic.
-- The corresponding Haskell function needs to be in scope for
-- it to be used in the logic.

{-@ define isNegative n = (n < 0) @-}
{-@ isNegative :: (Num a, Ord a) => {n:a | Negative n} -> {v:Bool | v = True}@-}
isNegative :: (Num a, Ord a) => a -> Bool
isNegative n = n  < 0

{-@ inline successor @-}
successor :: Int -> Int
successor n = n + 1

-- Local uses

{-@ negValue :: { x:Int | x > 0 } -> { y:Int | isNegative y} @-}
negValue :: Int -> Int
negValue = negate

{-@ successorGT :: n:Int -> { _:() | successor n > n}@-}
successorGT :: Int -> ()
successorGT = undefined

-- Using predicate aliases allows library authors to enforce domain specific
-- constraints while given access to predicates dependent on implementation details
-- without exporting them.

{-@ measure unSetS @-}
data SetS = SetS { unSetS :: Set Int }

{-@ predicate Member E S = Set.member E (unSetS S) @-}

{-@ addToEmptySetS :: n:Int -> { s:SetS | unSetS s = Set.empty }
                   -> { v:SetS | unSetS v = Set.singleton n } @-}
addToEmptySetS :: Int -> SetS -> SetS
addToEmptySetS n = SetS . (Set.insert n) . unSetS

{-@ emptySetS :: { s:SetS | unSetS s = Set.empty }@-}
emptySetS :: SetS
emptySetS = SetS $ Set.empty
