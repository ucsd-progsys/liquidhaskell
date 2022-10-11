{-|
  Purely functional top-down splay heaps.

   * D.D. Sleator and R.E. Rarjan,
     \"Self-Adjusting Binary Search Tree\",
     Journal of the Association for Computing Machinery,
     Vol 32, No 3, July 1985, pp 652-686.
     <http://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf>
-}

module Data.Heap.Splay (
  -- * Data structures
    Heap(..)
  , Splay(..)
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
  , partition
  , merge
  , minimum
  , valid
  , heapSort
  , showHeap
  , printHeap
  ) where

import Control.Applicative hiding (empty)
import Data.List (foldl', unfoldr)
import Data.Maybe
import Prelude hiding (minimum, maximum, null)

----------------------------------------------------------------

data Heap a = None | Some a (Splay a) deriving Show

instance (Eq a, Ord a) => Eq (Heap a) where
    h1 == h2 = heapSort h1 == heapSort h2

data Splay a = Leaf | Node (Splay a) a (Splay a) deriving Show

----------------------------------------------------------------

{-| Splitting smaller and bigger with splay.
    Since this is a heap implementation, members is not
    necessarily unique.
-}
partition :: Ord a => a -> Splay a -> (Splay a, Splay a)
partition _ Leaf = (Leaf, Leaf)
partition k x@(Node xl xk xr) = case compare k xk of
    LT -> case xl of
      Leaf          -> (Leaf, x)
      Node yl yk yr -> case compare k yk of
          LT -> let (lt, gt) = partition k yl        -- LL :zig zig
                in  (lt, Node gt yk (Node yr xk xr))
          _  -> let (lt, gt) = partition k yr        -- LR :zig zag
                in  (Node yl yk lt, Node gt xk xr)
    _ -> case xr of
      Leaf          -> (x, Leaf)
      Node yl yk yr -> case compare k yk of
          LT -> let (lt, gt) = partition k yl
                in  (Node xl xk lt, Node gt yk yr)   -- RL :zig zig
          _  -> let (lt, gt) = partition k yr        -- RR :zig zag
                in  (Node (Node xl xk yl) yk lt, gt)

----------------------------------------------------------------

{-| Empty heap.
-}

empty :: Heap a
empty = None

{-|
See if the heap is empty.

>>> Data.Heap.Splay.null empty
True
>>> Data.Heap.Splay.null (singleton 1)
False
-}

null :: Heap a -> Bool
null None = True
null _    = False

{-| Singleton heap.
-}

singleton :: a -> Heap a
singleton x = Some x (Node Leaf x Leaf)

----------------------------------------------------------------

{-| Insertion.

>>> insert 7 (fromList [5,3]) == fromList [3,5,7]
True
>>> insert 5 empty            == singleton 5
True
-}

insert :: Ord a => a -> Heap a -> Heap a
insert x None = singleton x
insert x (Some m t) = Some m' $ Node l x r
  where
    m' = min x m
    (l,r) = partition x t

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
toList None       = []
toList (Some _ t) = inorder t []
  where
    inorder Leaf xs = xs
    inorder (Node l x r) xs = inorder l (x : inorder r xs)

----------------------------------------------------------------

{-| Finding the minimum element.

>>> minimum (fromList [3,5,1])
Just 1
>>> minimum empty
Nothing
-}

minimum :: Heap a -> Maybe a
minimum None       = Nothing
minimum (Some m _) = Just m

----------------------------------------------------------------

{-| Deleting the minimum element.

>>> deleteMin (fromList [5,3,7]) == fromList [5,7]
True
>>> deleteMin empty == empty
True
-}

deleteMin :: Heap a -> Heap a
deleteMin None       = None
deleteMin (Some _ t) = fromMaybe None $ do
    t' <- deleteMin' t
    m  <- findMin' t'
    return $ Some m t'

deleteMin2 :: Heap a -> Maybe (a, Heap a)
deleteMin2 None       = Nothing
deleteMin2 h = (\m -> (m, deleteMin h)) <$> minimum h

-- deleteMin' and findMin' cannot be implemented together

deleteMin' :: Splay a -> Maybe (Splay a)
deleteMin' Leaf                        = Nothing
deleteMin' (Node Leaf _ r)             = Just r
deleteMin' (Node (Node Leaf _ lr) x r) = Just (Node lr x r)
deleteMin' (Node (Node ll lx lr) x r)  = let Just t = deleteMin' ll
                                         in Just (Node t lx (Node lr x r))

findMin' :: Splay a -> Maybe a
findMin' Leaf            = Nothing
findMin' (Node Leaf x _) = Just x
findMin' (Node l _ _)    = findMin' l

----------------------------------------------------------------
{-| Merging two heaps

>>> merge (fromList [5,3]) (fromList [5,7]) == fromList [3,5,5,7]
True
-}

merge :: Ord a => Heap a -> Heap a -> Heap a
merge None t = t
merge t None = t
merge (Some m1 t1) (Some m2 t2) = Some m t
  where
    m = min m1 m2
    t = merge' t1 t2

merge' :: Ord a => Splay a -> Splay a -> Splay a
merge' Leaf t = t
merge' (Node a x b) t = Node (merge' ta a) x (merge' tb b)
  where
    (ta,tb) = partition x t

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

showHeap :: Show a => Splay a -> String
showHeap = showHeap' ""

showHeap' :: Show a => String -> Splay a -> String
showHeap' _ Leaf = "\n"
showHeap' pref (Node l x r) = show x ++ "\n"
                        ++ pref ++ "+ " ++ showHeap' pref' l
                        ++ pref ++ "+ " ++ showHeap' pref' r
  where
    pref' = "  " ++ pref

printHeap :: Show a => Splay a -> IO ()
printHeap = putStr . showHeap

{-
Demo: http://www.link.cs.cmu.edu/splay/
Paper: http://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf
TopDown: http://www.cs.umbc.edu/courses/undergraduate/341/fall02/Lectures/Splay/TopDownSplay.ppt
Blog: http://chasen.org/~daiti-m/diary/?20061223
      http://www.geocities.jp/m_hiroi/clisp/clispb07.html


               fromList    minimum          delMin          member
Blanced Tree   N log N     log N            log N           log N
Skew Heap      N log N     1                log N(???)      N/A
Splay Heap     N           log N or A(N)?   log N or A(N)?  log N or A(N)?

-}
