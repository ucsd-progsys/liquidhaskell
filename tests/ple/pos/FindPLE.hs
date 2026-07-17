{-@ LIQUID "--ple" @-}
{-@ LIQUID "--etabeta" @-}
{-@ LIQUID "--higherorder" @-}

-- | Tests that PLE unfolds the `find` specification correctly.
module FindPLE where

import Data.Foldable (find)

{-@ data A = A { val  :: Int } @-}
data A = A { val  :: Int }

-- | A simple `find` wrapper that must expose its postcondition:
-- its 'Maybe' output is refined by its predicate argument.
-- PLE must be able to unfold it and make it surface. 
{-@ findVal :: x:Int -> [A] -> Maybe ({v:A | val v == x}) @-}
findVal :: Int -> [A] -> Maybe A
findVal x = find (\a -> val a == x)
