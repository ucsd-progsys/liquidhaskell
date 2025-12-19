-- | A stripped-down copy of @ExprAliases@ to test expression alias name ambiguity.
-- See @ReExportExprAliases@ for details.
module ExprAliasesCopycat (isNegative, successor, SetS, addToEmptySetS, emptySetS) where

import Data.Set (Set)
import qualified Data.Set as Set

-- This alias differs from the one in @ExprAliases@.
{-@ predicate InSomeRange X = X >= 11 && X <= 20 @-}

{-@ predicate Divides X Y = (Y mod X) = 0 @-}

{-@ predicate Negative X = X < 0 @-}

{-@ predicate LessThanSomeNum X =  X < 3 @-}

{-@ define isNegative n = (n < 0) @-}
{-@ isNegative :: (Num a, Ord a) => {n:a | Negative n} -> {v:Bool | v = True}@-}
isNegative :: (Num a, Ord a) => a -> Bool
isNegative n = n  < 0

{-@ inline successor @-}
successor :: Int -> Int
successor n = n + 1

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
