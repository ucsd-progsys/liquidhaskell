{-|
  Purely functional red-black trees.

    * Chris Okasaki, \"Red-Black Trees in a Functional Setting\",
	  Journal of Functional Programming, 9(4), pp 471-477, July 1999
      <http://www.eecs.usma.edu/webs/people/okasaki/pubs.html#jfp99>

    * Stefan Kahrs, \"Red-black trees with types\",
      Journal of functional programming, 11(04), pp 425-432, July 2001
-}

module Data.Set.RBTree (
  -- * Data structures
    RBTree(..)
  , Color(..)
  , BlackHeight
  -- * Creating red-black trees
  , empty
  , singleton
  , insert
  , fromList
  -- * Converting to a list
  , toList
  -- * Membership
  , member
  -- * Deleting
  , delete
  , deleteMin
  , deleteMax
  -- * Checking
  , null
  -- * Set operations
  , union
  , intersection
  , difference
  -- * Helper functions
  , join
  , merge
  , split
  , minimum
  , maximum
  , valid
  , showSet
  , printSet
  ) where

import Data.List (foldl')
import Prelude hiding (minimum, maximum, null)

----------------------------------------------------------------
-- Part to be shared
----------------------------------------------------------------

data RBTree a = Leaf -- color is Black
              | Node Color !BlackHeight !(RBTree a) a !(RBTree a)
              deriving (Show)

data Color = B -- ^ Black
           | R -- ^ Red
           deriving (Eq,Show)

{-|
  Red nodes have the same BlackHeight of their parent.
-}
type BlackHeight = Int

----------------------------------------------------------------

instance (Eq a) => Eq (RBTree a) where
    t1 == t2 = toList t1 == toList t2

----------------------------------------------------------------

height :: RBTree a -> BlackHeight
height Leaf = 0
height (Node _ h _ _ _) = h

----------------------------------------------------------------

{-|
See if the red black tree is empty.

>>> Data.Set.RBTree.null empty
True
>>> Data.Set.RBTree.null (singleton 1)
False
-}

null :: Eq a => RBTree a -> Bool
null t = t == Leaf

----------------------------------------------------------------

{-| Empty tree.

>>> height empty
0
-}

empty :: RBTree a
empty = Leaf

{-| Singleton tree.

>>> height (singleton 'a')
1
-}

singleton :: Ord a => a -> RBTree a
singleton x = Node B 1 Leaf x Leaf

----------------------------------------------------------------

{-| Creating a tree from a list. O(N log N)

>>> empty == fromList []
True
>>> singleton 'a' == fromList ['a']
True
>>> fromList [5,3,5] == fromList [5,3]
True
-}

fromList :: Ord a => [a] -> RBTree a
fromList = foldl' (flip insert) empty

----------------------------------------------------------------

{-| Creating a list from a tree. O(N)

>>> toList (fromList [5,3])
[3,5]
>>> toList empty
[]
-}

toList :: RBTree a -> [a]
toList t = inorder t []
  where
    inorder Leaf xs = xs
    inorder (Node _ _ l x r) xs = inorder l (x : inorder r xs)

----------------------------------------------------------------

{-| Checking if this element is a member of a tree?

>>> member 5 (fromList [5,3])
True
>>> member 1 (fromList [5,3])
False
-}

member :: Ord a => a -> RBTree a -> Bool
member _ Leaf = False
member x (Node _ _ l y r) = case compare x y of
    LT -> member x l
    GT -> member x r
    EQ -> True

----------------------------------------------------------------

isBalanced :: RBTree a -> Bool
isBalanced t = isBlackSame t && isRedSeparate t

isBlackSame :: RBTree a -> Bool
isBlackSame t = all (n==) ns
  where
    n:ns = blacks t

blacks :: RBTree a -> [Int]
blacks = blacks' 0
  where
    blacks' n Leaf = [n+1]
    blacks' n (Node R _ l _ r) = blacks' n  l ++ blacks' n  r
    blacks' n (Node B _ l _ r) = blacks' n' l ++ blacks' n' r
      where
        n' = n + 1

isRedSeparate :: RBTree a -> Bool
isRedSeparate = reds B

reds :: Color -> RBTree t -> Bool
reds _ Leaf = True
reds R (Node R _ _ _ _) = False
reds _ (Node c _ l _ r) = reds c l && reds c r

isOrdered :: Ord a => RBTree a -> Bool
isOrdered t = ordered $ toList t
  where
    ordered [] = True
    ordered [_] = True
    ordered (x:y:xys) = x < y && ordered (y:xys)

blackHeight :: RBTree a -> Bool
blackHeight Leaf = True
blackHeight t@(Node B i _ _ _) = bh i t
  where
    bh n Leaf = n == 0
    bh n (Node R h l _ r) = n == h' && bh n l && bh n r
      where
        h' = h - 1
    bh n (Node B h l _ r) = n == h && bh n' l && bh n' r
      where
        n' = n - 1
blackHeight _ = error "blackHeight"

----------------------------------------------------------------

turnR :: RBTree a -> RBTree a
turnR Leaf             = error "turnR"
turnR (Node _ h l x r) = Node R h l x r

turnB :: RBTree a -> RBTree a
turnB Leaf           = error "turnB"
turnB (Node _ h l x r) = Node B h l x r

turnB' :: RBTree a -> RBTree a
turnB' Leaf             = Leaf
turnB' (Node _ h l x r) = Node B h l x r

----------------------------------------------------------------

{-| Finding the minimum element. O(log N)

>>> minimum (fromList [3,5,1])
1
>>> minimum empty
*** Exception: minimum
-}

minimum :: RBTree a -> a
minimum (Node _ _ Leaf x _) = x
minimum (Node _ _ l _ _)    = minimum l
minimum _                   = error "minimum"

{-| Finding the maximum element. O(log N)

>>> maximum (fromList [3,5,1])
5
>>> maximum empty
*** Exception: maximum
-}

maximum :: RBTree a -> a
maximum (Node _ _ _ x Leaf) = x
maximum (Node _ _ _ _ r)    = maximum r
maximum _                   = error "maximum"

----------------------------------------------------------------

showSet :: Show a => RBTree a -> String
showSet = showSet' ""

showSet' :: Show a => String -> RBTree a -> String
showSet' _ Leaf = "\n"
showSet' pref (Node k h l x r) = show k ++ " " ++ show x ++ " (" ++ show h ++ ")\n"
                              ++ pref ++ "+ " ++ showSet' pref' l
                              ++ pref ++ "+ " ++ showSet' pref' r
  where
    pref' = "  " ++ pref

printSet :: Show a => RBTree a -> IO ()
printSet = putStr . showSet

----------------------------------------------------------------

isRed :: RBTree a -> Bool
isRed (Node R _ _ _ _ ) = True
isRed _               = False

----------------------------------------------------------------
-- Basic operations
----------------------------------------------------------------

{-| Checking validity of a tree.
-}

valid :: Ord a => RBTree a -> Bool
valid t = isBalanced t && blackHeight t && isOrdered t

----------------------------------------------------------------
-- Chris Okasaki
--

{-| Insertion. O(log N)

>>> insert 5 (fromList [5,3]) == fromList [3,5]
True
>>> insert 7 (fromList [5,3]) == fromList [3,5,7]
True
>>> insert 5 empty            == singleton 5
True
-}

insert :: Ord a => a -> RBTree a -> RBTree a
insert kx t = turnB (insert' kx t)

insert' :: Ord a => a -> RBTree a -> RBTree a
insert' kx Leaf = Node R 1 Leaf kx Leaf
insert' kx s@(Node B h l x r) = case compare kx x of
    LT -> balanceL' h (insert' kx l) x r
    GT -> balanceR' h l x (insert' kx r)
    EQ -> s
insert' kx s@(Node R h l x r) = case compare kx x of
    LT -> Node R h (insert' kx l) x r
    GT -> Node R h l x (insert' kx r)
    EQ -> s

balanceL' :: BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceL' h (Node R _ (Node R _ a x b) y c) z d =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceL' h (Node R _ a x (Node R _ b y c)) z d =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceL' h l x r = Node B h l x r

balanceR' :: BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceR' h a x (Node R _ b y (Node R _ c z d)) =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceR' h a x (Node R _ (Node R _ b y c) z d) =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceR' h l x r = Node B h l x r

----------------------------------------------------------------

balanceL :: Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceL B h (Node R _ (Node R _ a x b) y c) z d =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceL B h (Node R _ a x (Node R _ b y c)) z d =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceL k h l x r = Node k h l x r

balanceR :: Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceR B h a x (Node R _ b y (Node R _ c z d)) =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceR B h a x (Node R _ (Node R _ b y c) z d) =
    Node R (h+1) (Node B h a x b) y (Node B h c z d)
balanceR k h l x r = Node k h l x r

----------------------------------------------------------------

type RBTreeBDel a = (RBTree a, Bool)

unbalancedL :: Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTreeBDel a
unbalancedL c h l@(Node B _ _ _ _) x r
  = (balanceL B h (turnR l) x r, c == B)
unbalancedL B h (Node R lh ll lx lr@(Node B _ _ _ _)) x r
  = (Node B lh ll lx (balanceL B h (turnR lr) x r), False)
unbalancedL _ _ _ _ _ = error "unbalancedL"

-- The left tree lacks one Black node
unbalancedR :: Color -> BlackHeight -> RBTree a -> a -> RBTree a -> (RBTree a, Bool)
-- Decreasing one Black node in the right
unbalancedR c h l x r@(Node B _ _ _ _)
  = (balanceR B h l x (turnR r), c == B)
-- Taking one Red node from the right and adding it to the right as Black
unbalancedR B h l x (Node R rh rl@(Node B _ _ _ _) rx rr)
  = (Node B rh (balanceR B h l x (turnR rl)) rx rr, False)
unbalancedR _ _ _ _ _ = error "unbalancedR"

----------------------------------------------------------------

{-| Deleting the minimum element. O(log N)

>>> deleteMin (fromList [5,3,7]) == fromList [5,7]
True
>>> deleteMin empty == empty
True
-}

deleteMin :: RBTree a -> RBTree a
deleteMin Leaf = empty
deleteMin t = turnB' s
  where
    ((s, _), _) = deleteMin' t

deleteMin' :: RBTree a -> (RBTreeBDel a, a)
deleteMin' Leaf                           = error "deleteMin'"
deleteMin' (Node B _ Leaf x Leaf)         = ((Leaf, True), x)
deleteMin' (Node B _ Leaf x r@(Node R _ _ _ _)) = ((turnB r, False), x)
deleteMin' (Node R _ Leaf x r)            = ((r, False), x)
deleteMin' (Node c h l x r)               = if d then (tD, m) else (tD', m)
  where
    ((l',d),m) = deleteMin' l
    tD  = unbalancedR c (h-1) l' x r
    tD' = (Node c h l' x r, False)

----------------------------------------------------------------

{-| Deleting the maximum

>>> deleteMax (fromList [(5,"a"), (3,"b"), (7,"c")]) == fromList [(3,"b"), (5,"a")]
True
>>> deleteMax empty == empty
True
-}

deleteMax :: RBTree a -> RBTree a
deleteMax Leaf = empty
deleteMax t = turnB' s
  where
    ((s, _), _) = deleteMax' t

deleteMax' :: RBTree a -> (RBTreeBDel a, a)
deleteMax' Leaf                           = error "deleteMax'"
deleteMax' (Node B _ Leaf x Leaf)         = ((Leaf, True), x)
deleteMax' (Node B _ l@(Node R _ _ _ _) x Leaf) = ((turnB l, False), x)
deleteMax' (Node R _ l x Leaf)            = ((l, False), x)
deleteMax' (Node c h l x r)               = if d then (tD, m) else (tD', m)
  where
    ((r',d),m) = deleteMax' r
    tD  = unbalancedL c (h-1) l x r'
    tD' = (Node c h l x r', False)

----------------------------------------------------------------

blackify :: RBTree a -> RBTreeBDel a
blackify s@(Node R _ _ _ _) = (turnB s, False)
blackify s                  = (s, True)

{-| Deleting this element from a tree. O(log N)

>>> delete 5 (fromList [5,3]) == singleton 3
True
>>> delete 7 (fromList [5,3]) == fromList [3,5]
True
>>> delete 5 empty            == empty
True
-}

delete :: Ord a => a -> RBTree a -> RBTree a
delete x t = turnB' s
  where
    (s,_) = delete' x t

delete' :: Ord a => a -> RBTree a -> RBTreeBDel a
delete' _ Leaf = (Leaf, False)
delete' x (Node c h l y r) = case compare x y of
    LT -> let (l',d) = delete' x l
              t = Node c h l' y r
          in if d then unbalancedR c (h-1) l' y r else (t, False)
    GT -> let (r',d) = delete' x r
              t = Node c h l y r'
          in if d then unbalancedL c (h-1) l y r' else (t, False)
    EQ -> case r of
        Leaf -> if c == B then blackify l else (l, False)
        _ -> let ((r',d),m) = deleteMin' r
                 t = Node c h l m r'
             in if d then unbalancedL c (h-1) l m r' else (t, False)

----------------------------------------------------------------
-- Set operations
----------------------------------------------------------------

{-| Joining two trees with an element. O(log N)

    Each element of the left tree must be less than the element.
    Each element of the right tree must be greater than the element.
    Both tree must have black root.
-}

join :: Ord a => RBTree a -> a -> RBTree a -> RBTree a
join Leaf g t2 = insert g t2
join t1 g Leaf = insert g t1
join t1 g t2 = case compare h1 h2 of
    LT -> turnB $ joinLT t1 g t2 h1
    GT -> turnB $ joinGT t1 g t2 h2
    EQ -> Node B (h1+1) t1 g t2
  where
    h1 = height t1
    h2 = height t2

-- The root of result must be red.
joinLT :: Ord a => RBTree a -> a -> RBTree a -> BlackHeight -> RBTree a
joinLT t1 g t2@(Node c h l x r) h1
  | h == h1   = Node R (h+1) t1 g t2
  | otherwise = balanceL c h (joinLT t1 g l h1) x r
joinLT _ _ _ _ = error "joinLT"

-- The root of result must be red.
joinGT :: Ord a => RBTree a -> a -> RBTree a -> BlackHeight -> RBTree a
joinGT t1@(Node c h l x r) g t2 h2
  | h == h2   = Node R (h+1) t1 g t2
  | otherwise = balanceR c h l x (joinGT r g t2 h2)
joinGT _ _ _ _ = error "joinGT"

----------------------------------------------------------------

{-| Merging two trees. O(log N)

    Each element of the left tree must be less than each element of
    the right tree. Both trees must have black root.
-}

merge :: Ord a => RBTree a -> RBTree a -> RBTree a
merge Leaf t2 = t2
merge t1 Leaf = t1
merge t1 t2 = case compare h1 h2 of
    LT -> turnB $ mergeLT t1 t2 h1
    GT -> turnB $ mergeGT t1 t2 h2
    EQ -> turnB $ mergeEQ t1 t2
  where
    h1 = height t1
    h2 = height t2

mergeLT :: Ord a => RBTree a -> RBTree a -> BlackHeight -> RBTree a
mergeLT t1 t2@(Node c h l x r) h1
  | h == h1   = mergeEQ t1 t2
  | otherwise = balanceL c h (mergeLT t1 l h1) x r
mergeLT _ _ _ = error "mergeLT"

mergeGT :: Ord a => RBTree a -> RBTree a -> BlackHeight -> RBTree a
mergeGT t1@(Node c h l x r) t2 h2
  | h == h2   = mergeEQ t1 t2
  | otherwise = balanceR c h l x (mergeGT r t2 h2)
mergeGT _ _ _ = error "mergeGT"

{-
  Merging two trees whose heights are the same.
  The root must be either
     a red with height + 1
  for
     a black with height
-}

mergeEQ :: Ord a => RBTree a -> RBTree a -> RBTree a
mergeEQ Leaf Leaf = Leaf
mergeEQ t1@(Node _ h l x r) t2
  | h == h2'  = Node R (h+1) t1 m t2'
  | isRed l   = Node R (h+1) (turnB l) x (Node B h r m t2')
  -- unnecessary for LL
  | isRed r   = Node B h (Node R h l x rl) rx (Node R h rr m t2')
  | otherwise = Node B h (turnR t1) m t2'
  where
    m  = minimum t2
    t2' = deleteMin t2
    h2' = height t2'
    Node R _ rl rx rr = r
mergeEQ _ _ = error "mergeEQ"

----------------------------------------------------------------

{-| Splitting a tree. O(log N)

>>> split 2 (fromList [5,3]) == (empty, fromList [3,5])
True
>>> split 3 (fromList [5,3]) == (empty, singleton 5)
True
>>> split 4 (fromList [5,3]) == (singleton 3, singleton 5)
True
>>> split 5 (fromList [5,3]) == (singleton 3, empty)
True
>>> split 6 (fromList [5,3]) == (fromList [3,5], empty)
True
-}

split :: Ord a => a -> RBTree a -> (RBTree a, RBTree a)
split _ Leaf = (Leaf,Leaf)
split kx (Node _ _ l x r) = case compare kx x of
    LT -> (lt, join gt x (turnB' r)) where (lt,gt) = split kx l
    GT -> (join (turnB' l) x lt, gt) where (lt,gt) = split kx r
    EQ -> (turnB' l, turnB' r)

{- LL
split :: Ord a => a -> RBTree a -> (RBTree a, RBTree a)
split _ Leaf = (Leaf,Leaf)
split kx (Node _ _ l x r) = case compare kx x of
    LT -> (lt, join gt x r) where (lt,gt) = split kx l
    GT -> (join l x lt, gt) where (lt,gt) = split kx r
    EQ -> (turnB' l, r)
-}

----------------------------------------------------------------

{-| Creating a union tree from two trees. O(N + M)

>>> union (fromList [5,3]) (fromList [5,7]) == fromList [3,5,7]
True
-}

union :: Ord a => RBTree a -> RBTree a -> RBTree a
union t1 Leaf = t1 -- ensured Black thanks to split
union Leaf t2 = turnB' t2
union t1 (Node _ _ l x r) = join (union l' l) x (union r' r)
  where
    (l',r') = split x t1

{-| Creating a intersection tree from trees. O(N + N)

>>> intersection (fromList [5,3]) (fromList [5,7]) == singleton 5
True
-}

intersection :: Ord a => RBTree a -> RBTree a -> RBTree a
intersection Leaf _ = Leaf
intersection _ Leaf = Leaf
intersection t1 (Node _ _ l x r)
  | member x t1 = join (intersection l' l) x (intersection r' r)
  | otherwise   = merge (intersection l' l) (intersection r' r)
  where
    (l',r') = split x t1

{-| Creating a difference tree from trees. O(N + N)

>>> difference (fromList [5,3]) (fromList [5,7]) == singleton 3
True
-}

difference :: Ord a => RBTree a -> RBTree a -> RBTree a
difference Leaf _  = Leaf
difference t1 Leaf = t1 -- ensured Black thanks to split
difference t1 (Node _ _ l x r) = merge (difference l' l) (difference r' r)
  where
    (l',r') = split x t1
