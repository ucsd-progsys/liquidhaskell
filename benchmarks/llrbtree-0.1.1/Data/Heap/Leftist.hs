{-|
  Leftist Heap

  - the fun of programming
-}

module Data.Heap.Leftist (
  -- * Data structures
    Leftist(..)
  , Rank
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

data Leftist a = Leaf | Node Rank (Leftist a) a (Leftist a) deriving Show

instance (Eq a, Ord a) => Eq (Leftist a) where
    h1 == h2 = heapSort h1 == heapSort h2

type Rank = Int

----------------------------------------------------------------

rank :: Leftist a -> Rank
rank Leaf           = 0
rank (Node v _ _ _) = v

----------------------------------------------------------------

{-| Empty heap.
-}

empty :: Leftist a
empty = Leaf

{-|
See if the heap is empty.

>>> Data.Heap.Leftist.null empty
True
>>> Data.Heap.Leftist.null (singleton 1)
False
-}

null :: Leftist t -> Bool
null Leaf           = True
null (Node _ _ _ _) = False

{-| Singleton heap.
-}

singleton :: a -> Leftist a
singleton x = Node 1 Leaf x Leaf

----------------------------------------------------------------

{-| Insertion.

>>> insert 7 (fromList [5,3]) == fromList [3,5,7]
True
>>> insert 5 empty            == singleton 5
True
-}

insert :: Ord a => a -> Leftist a -> Leftist a
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

fromList :: Ord a => [a] -> Leftist a
fromList = foldl' (flip insert) empty

----------------------------------------------------------------

{-| Creating a list from a heap. O(N)

>>> let xs = [5,3,5]
>>> length (toList (fromList xs)) == length xs
True
>>> toList empty
[]
-}

toList :: Leftist a -> [a]
toList t = inorder t []
  where
    inorder Leaf xs           = xs
    inorder (Node _ l x r) xs = inorder l (x : inorder r xs)

----------------------------------------------------------------

{-| Finding the minimum element.

>>> minimum (fromList [3,5,1])
Just 1
>>> minimum empty
Nothing
-}

minimum :: Leftist a -> Maybe a
minimum Leaf           = Nothing
minimum (Node _ _ x _) = Just x

----------------------------------------------------------------

{-| Deleting the minimum element.

>>> deleteMin (fromList [5,3,7]) == fromList [5,7]
True
>>> deleteMin empty == empty
True
-}

deleteMin :: Ord a => Leftist a -> Leftist a
deleteMin Leaf           = Leaf
deleteMin (Node _ l _ r) = merge l r

deleteMin2 :: Ord a => Leftist a -> Maybe (a, Leftist a)
deleteMin2 Leaf = Nothing
deleteMin2 h    = (\m -> (m, deleteMin h)) <$> minimum h

----------------------------------------------------------------
{-| Merging two heaps

>>> merge (fromList [5,3]) (fromList [5,7]) == fromList [3,5,5,7]
True
-}

merge :: Ord a => Leftist a -> Leftist a -> Leftist a
merge t1 Leaf = t1
merge Leaf t2 = t2
merge t1@(Node _ l1 x1 r1) t2@(Node _ l2 x2 r2)
  | x1 <= x2  = join l1 x1 (merge r1 t2)
  | otherwise = join l2 x2 (merge t1 r2)

join :: Ord a => Leftist a -> a -> Leftist a -> Leftist a
join t1 x t2
  | rank t1 >= rank t2 = Node (rank t2 + 1) t1 x t2
  | otherwise          = Node (rank t1 + 1) t2 x t1

----------------------------------------------------------------
-- Basic operations
----------------------------------------------------------------

{-| Checking validity of a heap.
-}

valid :: Ord a => Leftist a -> Bool
valid t = isOrdered (heapSort t)

heapSort :: Ord a => Leftist a -> [a]
heapSort t = unfoldr deleteMin2 t

isOrdered :: Ord a => [a] -> Bool
isOrdered [] = True
isOrdered [_] = True
isOrdered (x:y:xys) = x <= y && isOrdered (y:xys) -- allowing duplicated keys
