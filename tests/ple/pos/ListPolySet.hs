{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module ListPolySet where

import Prelude hiding (all)
import Data.Set hiding (all)
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect assert @-}
{-@ assert :: b:{Bool | b } -> x:a -> {v:a | v == x && b} @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ reflect ?? @-}
x ?? y = y

{-@ reflect all @-}
all :: (a -> Bool) -> [a] -> Bool
all _ []       = True
all p (x : xs) = p x && all p xs

{-@ all_to_elem :: (Ord a, Eq a) => f:(a -> Bool)
                -> ls:{[a] | all f ls}
                -> e:{a | (member e (fromList ls))}
                -> { f e } @-}
all_to_elem :: (Ord a, Eq a) => (a -> Bool) -> [a] -> a -> ()
all_to_elem _ []       _ = ()
all_to_elem f (x : xs) e | x == e
  = assert (all f (x : xs)) ()
                         | otherwise
  = assert (all f (x : xs)) ()
    ? assert (all f xs) ()
    ? member e (fromList xs)
    ? all_to_elem f xs e

{-@ all_subset :: f:(a -> Bool)
               -> ls1:{[a] | all (f) ls1 }
               -> ls2:{[a] | isSubsetOf (fromList ls2) (fromList ls1) }
               -> { all f ls2 } @-}
all_subset :: Ord a => (a -> Bool) -> [a] -> [a] -> ()
all_subset f ls1 (x : ls2) =
  assert (member x (fromList ls1)) ()
    ?? all_to_elem f ls1 x
    ?? all_subset f ls1 ls2
all_subset f _ _ = ()