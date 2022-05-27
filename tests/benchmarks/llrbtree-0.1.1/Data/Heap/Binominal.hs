{-|
  Binominal Heap

  - the fun of programming
-}

module Data.Heap.Binominal (
  -- * Data structures
    Heap(..)
  , Tree(..)
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
import qualified Prelude as L (null)

----------------------------------------------------------------

type Rank = Int

data Tree a =
    -- | Rank, a minimum root element, trees
    Node Rank a [Tree a] deriving Show

newtype Heap a = Heap [Tree a] deriving Show

instance (Eq a, Ord a) => Eq (Heap a) where
    h1 == h2 = heapSort h1 == heapSort h2

----------------------------------------------------------------

rank :: Tree a -> Rank
rank (Node r _ _) = r

root :: Tree a -> a
root (Node _ x _) = x

link :: Ord a => Tree a -> Tree a -> Tree a
link t1@(Node r1 x1 ts1) t2@(Node r2 x2 ts2)
  | x1 <= x2  = Node (r1+1) x1 (t2:ts1)
  | otherwise = Node (r2+1) x2 (t1:ts2)

----------------------------------------------------------------

{-| Empty heap.
-}

empty :: Heap a
empty = Heap []

{-|
See if the heap is empty.

>>> Data.Heap.Binominal.null empty
True
>>> Data.Heap.Binominal.null (singleton 1)
False
-}

null :: Heap a -> Bool
null (Heap ts) = L.null ts

{-| Singleton heap.
-}

singleton :: a -> Heap a
singleton x = Heap [Node 0 x []]

----------------------------------------------------------------

{-| Insertion.

>>> insert 7 (fromList [5,3]) == fromList [3,5,7]
True
>>> insert 5 empty            == singleton 5
True
-}

insert :: Ord a => a -> Heap a -> Heap a
insert x (Heap ts) = Heap (insert' (Node 0 x []) ts)

insert' :: Ord a => Tree a -> [Tree a] -> [Tree a]
insert' t [] = [t]
insert' t ts@(t':ts')
  | rank t < rank t' = t : ts
  | otherwise        = insert' (link t t') ts'

----------------------------------------------------------------

{-| Creating a heap from a list.

>>> empty == fromList []
True
>>> singleton 'a' == fromList ['a']
True
>>> fromList [5,3] == fromList [5,3]
True
-}

fromList :: Ord a => [a] -> Heap a
fromList = foldl' (flip insert) empty

----------------------------------------------------------------

{-| Creating a list from a heap. O(N)

>>> let xs = [5,3,5]
>>> length (toList (fromList xs)) == length xs
True
>>> toList empty
[]
-}

toList :: Heap a -> [a]
toList (Heap ts) = concatMap toList' ts

toList' :: Tree a -> [a]
toList' (Node _ x []) = [x]
toList' (Node _ x ts) = x : concatMap toList' ts

----------------------------------------------------------------

{-| Finding the minimum element.

>>> minimum (fromList [3,5,1])
Just 1
>>> minimum empty
Nothing
-}

minimum :: Ord a => Heap a -> Maybe a
minimum (Heap ts) = root . fst <$> deleteMin' ts

----------------------------------------------------------------

{-| Deleting the minimum element.

>>> deleteMin (fromList [5,3,7]) == fromList [5,7]
True
>>> deleteMin empty == empty
True
-}

deleteMin :: Ord a => Heap a -> Heap a
deleteMin (Heap ts) = case deleteMin' ts of
    Nothing                  -> empty
    Just (Node _ _ ts1, ts2) -> Heap (merge' (reverse ts1) ts2)

deleteMin2 :: Ord a => Heap a -> Maybe (a, Heap a)
deleteMin2 (Heap []) = Nothing
deleteMin2 h         = (\m -> (m, deleteMin h)) <$> minimum h

deleteMin' :: Ord a => [Tree a] -> Maybe (Tree a, [Tree a])
deleteMin' []     = Nothing
deleteMin' [t]    = Just (t,[])
deleteMin' (t:ts)
  | root t < root t' = Just (t,  ts)
  | otherwise        = Just (t', t:ts')
  where
    Just (t',ts')    = deleteMin' ts

----------------------------------------------------------------
{-| Merging two heaps

>>> merge (fromList [5,3]) (fromList [5,7]) == fromList [3,5,5,7]
True
-}

merge :: Ord a => Heap a -> Heap a -> Heap a
merge (Heap ts1) (Heap ts2) = Heap (merge' ts1 ts2)

merge' :: Ord a => [Tree a] -> [Tree a] -> [Tree a]
merge' ts1 [] = ts1
merge' [] ts2 = ts2
merge' ts1@(t1:ts1') ts2@(t2:ts2')
  | rank t1 < rank t2 = t1 : merge' ts1' ts2
  | rank t2 < rank t1 = t2 : merge' ts1 ts2'
  | otherwise         = insert' (link t1 t2) (merge' ts1' ts2')

----------------------------------------------------------------
-- Basic operations
----------------------------------------------------------------

{-| Checking validity of a heap.
-}

valid :: Ord a => Heap a -> Bool
valid t = isOrdered (heapSort t)

heapSort :: Ord a => Heap a -> [a]
heapSort t = unfoldr deleteMin2 t

isOrdered :: Ord a => [a] -> Bool
isOrdered [] = True
isOrdered [_] = True
isOrdered (x:y:xys) = x <= y && isOrdered (y:xys) -- allowing duplicated keys
