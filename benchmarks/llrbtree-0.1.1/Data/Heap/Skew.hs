{-|
  Skew Heap

  - the fun of programming
-}

module Data.Heap.Skew (
  -- * Data structures
    Skew(..)
  -- * Creating heaps
  , empty
  , singleton
  , insert
  , fromList
  -- * Converting to a list
  , toList
  -- * Deleting
  , deleteMin
  -- * Checking heaps
  , null
  -- * Helper functions
  , merge
  , minimum
  , valid
  , heapSort
  ) where

import Control.Applicative hiding (empty)
import Data.List (foldl', unfoldr)
import Data.Maybe
import Prelude hiding (minimum, maximum, null)

----------------------------------------------------------------

data Skew a = Leaf | Node (Skew a) a (Skew a) deriving Show

instance (Eq a, Ord a) => Eq (Skew a) where
    h1 == h2 = heapSort h1 == heapSort h2

----------------------------------------------------------------

{-| Empty heap.
-}

empty :: Skew a
empty = Leaf

{-|
See if the heap is empty.

>>> Data.Heap.Skew.null empty
True
>>> Data.Heap.Skew.null (singleton 1)
False
-}

null :: Skew t -> Bool
null Leaf         = True
null (Node _ _ _) = False

{-| Singleton heap.
-}

singleton :: a -> Skew a
singleton x = Node Leaf x Leaf

----------------------------------------------------------------

{-| Insertion.

>>> insert 7 (fromList [5,3]) == fromList [3,5,7]
True
>>> insert 5 empty            == singleton 5
True
-}

insert :: Ord a => a -> Skew a -> Skew a
insert x t = merge (singleton x) t

----------------------------------------------------------------

{-| Creating a heap from a list.

>>> empty == fromList []
True
>>> singleton 'a' == fromList ['a']
True
>>> fromList [5,3] == fromList [5,3]
True
-}

fromList :: Ord a => [a] -> Skew a
fromList = foldl' (flip insert) empty

----------------------------------------------------------------

{-| Creating a list from a heap. O(N)

>>> let xs = [5,3,5]
>>> length (toList (fromList xs)) == length xs
True
>>> toList empty
[]
-}

toList :: Skew a -> [a]
toList t = inorder t []
  where
    inorder Leaf xs         = xs
    inorder (Node l x r) xs = inorder l (x : inorder r xs)

----------------------------------------------------------------

{-| Finding the minimum element.

>>> minimum (fromList [3,5,1])
Just 1
>>> minimum empty
Nothing
-}

minimum :: Skew a -> Maybe a
minimum Leaf         = Nothing
minimum (Node _ x _) = Just x

----------------------------------------------------------------

{-| Deleting the minimum element.

>>> deleteMin (fromList [5,3,7]) == fromList [5,7]
True
>>> deleteMin empty == empty
True
-}

deleteMin :: Ord a => Skew a -> Skew a
deleteMin Leaf         = Leaf
deleteMin (Node l _ r) = merge l r

deleteMin2 :: Ord a => Skew a -> Maybe (a, Skew a)
deleteMin2 Leaf = Nothing
deleteMin2 h    = (\m -> (m, deleteMin h)) <$> minimum h

----------------------------------------------------------------
{-| Merging two heaps

>>> merge (fromList [5,3]) (fromList [5,7]) == fromList [3,5,5,7]
True
-}

merge :: Ord a => Skew a -> Skew a -> Skew a
merge t1 Leaf = t1
merge Leaf t2 = t2
merge t1 t2
  | minimum t1 <= minimum t2 = join t1 t2
  | otherwise                = join t2 t1

join :: Ord a => Skew a -> Skew a -> Skew a
join (Node l x r) t = Node r x (merge l t)
join _ _ = error "join"

----------------------------------------------------------------
-- Basic operations
----------------------------------------------------------------

{-| Checking validity of a heap.
-}

valid :: Ord a => Skew a -> Bool
valid t = isOrdered (heapSort t)

heapSort :: Ord a => Skew a -> [a]
heapSort t = unfoldr deleteMin2 t

isOrdered :: Ord a => [a] -> Bool
isOrdered [] = True
isOrdered [_] = True
isOrdered (x:y:xys) = x <= y && isOrdered (y:xys) -- allowing duplicated keys
