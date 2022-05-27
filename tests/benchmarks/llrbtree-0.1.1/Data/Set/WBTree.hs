{-|
  Purely functional weight balanced trees, aka trees of bounded balance.

    * J. Nievergelt and E.M. Reingold, \"Binary search trees of
      bounded balance\", Proceedings of the fourth annual ACM symposium on
      Theory of computing, pp 137-142, 1972.

    * S. Adams, \"Implementing sets efficiently in a functional language\",
      Technical Report CSTR 92-10, University of Southampton, 1992.
      <http://groups.csail.mit.edu/mac/users/adams/BB/>

    * S. Adam, \"Efficient sets: a balancing act\",
      Journal of Functional Programming, Vol 3, Issue 4, pp 553-562.

    * Y. Hirai and K. Yamamoto,
      \"Balancing Weight-Balanced Trees\",
      Journal of Functional Programming. Vol 21, Issue 03, pp 287-307.
      <http://mew.org/~kazu/proj/weight-balanced-tree/>

    * M. Strake, \"Adams' Trees Revisited - Correct and Efficient Implementation\",
      TFP 2011.
      <http://fox.ucw.cz/papers/bbtree/>
-}

module Data.Set.WBTree (
  -- * Data structures
    WBTree(..)
  , Size
  , size
  -- * Creating sets
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
--  , showTree
--  , printTree
  ) where

import Data.List (foldl')
import Prelude hiding (minimum, maximum, null)

----------------------------------------------------------------

type Size = Int
data WBTree a = Leaf | Node Size (WBTree a) a (WBTree a) deriving (Show)


instance (Eq a) => Eq (WBTree a) where
    t1 == t2 = toList t1 == toList t2

size :: WBTree a -> Size
size Leaf            = 0
size (Node sz _ _ _) = sz

----------------------------------------------------------------

{-|
See if the set is empty.

>>> Data.Set.WBTree.null empty
True
>>> Data.Set.WBTree.null (singleton 1)
False
-}

null :: Eq a => WBTree a -> Bool
null t = t == Leaf

----------------------------------------------------------------

{-| Empty set.

>>> size empty
0
-}

empty :: WBTree a
empty = Leaf

{-| Singleton set.

>>> size (singleton 'a')
1
-}

singleton :: a -> WBTree a
singleton x = Node 1 Leaf x Leaf

----------------------------------------------------------------

node :: WBTree a -> a -> WBTree a -> WBTree a
node l x r = Node (size l + size r + 1) l x r

----------------------------------------------------------------

{-| Insertion. O(log N)

>>> insert 5 (fromList [5,3]) == fromList [3,5]
True
>>> insert 7 (fromList [5,3]) == fromList [3,5,7]
True
>>> insert 5 empty            == singleton 5
True
-}

insert :: Ord a => a -> WBTree a -> WBTree a
insert k Leaf = singleton k
insert k (Node sz l x r) = case compare k x of
    LT -> balanceR (insert k l) x r
    GT -> balanceL l x (insert k r)
    EQ -> Node sz l x r

{-| Creating a set from a list. O(N log N)

>>> empty == fromList []
True
>>> singleton 'a' == fromList ['a']
True
>>> fromList [5,3,5] == fromList [5,3]
True
-}

fromList :: Ord a => [a] -> WBTree a
fromList = foldl' (flip insert) empty

----------------------------------------------------------------

{-| Creating a list from a set. O(N)

>>> toList (fromList [5,3])
[3,5]
>>> toList empty
[]
-}

toList :: WBTree a -> [a]
toList t = inorder t []
  where
    inorder Leaf xs           = xs
    inorder (Node _ l x r) xs = inorder l (x : inorder r xs)

----------------------------------------------------------------

{-| Checking if this element is a member of a set?

>>> member 5 (fromList [5,3])
True
>>> member 1 (fromList [5,3])
False
-}

member :: Ord a => a -> WBTree a -> Bool
member _ Leaf = False
member k (Node _ l x r) = case compare k x of
    LT -> member k l
    GT -> member k r
    EQ -> True

----------------------------------------------------------------

balanceL :: WBTree a -> a -> WBTree a -> WBTree a
balanceL l x r
  | isBalanced l r = node l x r
  | otherwise      = rotateL l x r

balanceR :: WBTree a -> a -> WBTree a -> WBTree a
balanceR l x r
  | isBalanced r l = node l x r
  | otherwise      = rotateR l x r

rotateL :: WBTree a -> a -> WBTree a -> WBTree a
rotateL l x r@(Node _ rl _ rr)
  | isSingle rl rr = singleL l x r
  | otherwise      = doubleL l x r
rotateL _ _ _      = error "rotateL"

rotateR :: WBTree a -> a -> WBTree a -> WBTree a
rotateR l@(Node _ ll _ lr) x r
  | isSingle lr ll = singleR l x r
  | otherwise      = doubleR l x r
rotateR _ _ _      = error "rotateR"

singleL :: WBTree a -> a -> WBTree a -> WBTree a
singleL l x (Node _ rl rx rr) = node (node l x rl) rx rr
singleL _ _ _                 = error "singleL"

singleR :: WBTree a -> a -> WBTree a -> WBTree a
singleR (Node _ ll lx lr) x r = node ll lx (node lr x r)
singleR _ _ _                 = error "singleR"

doubleL :: WBTree a -> a -> WBTree a -> WBTree a
doubleL l x (Node _ (Node _ rll rlx rlr) rx rr) = node (node l x rll) rlx (node rlr rx rr)
doubleL _ _ _                                   = error "doubleL"

doubleR :: WBTree a -> a -> WBTree a -> WBTree a
doubleR (Node _ ll lx (Node _ lrl lrx lrr)) x r = node (node ll lx lrl) lrx (node lrr x r)
doubleR _ _ _                                   = error "doubleR"

----------------------------------------------------------------

{-| Deleting the minimum element. O(log N)

>>> deleteMin (fromList [5,3,7]) == fromList [5,7]
True
>>> deleteMin empty == empty
True
-}

deleteMin :: WBTree a -> WBTree a
deleteMin (Node _ Leaf _ r) = r
deleteMin (Node _ l x r)    = balanceL (deleteMin l) x r
deleteMin Leaf              = Leaf

{-| Deleting the maximum

>>> deleteMax (fromList [(5,"a"), (3,"b"), (7,"c")]) == fromList [(3,"b"), (5,"a")]
True
>>> deleteMax empty == empty
True
-}

deleteMax :: WBTree a -> WBTree a
deleteMax (Node _ l _ Leaf) = l
deleteMax (Node _ l x r)    = balanceR l x (deleteMax r)
deleteMax Leaf              = Leaf

----------------------------------------------------------------

{-| Deleting this element from a set. O(log N)

>>> delete 5 (fromList [5,3]) == singleton 3
True
>>> delete 7 (fromList [5,3]) == fromList [3,5]
True
>>> delete 5 empty            == empty
True
-}

delete :: Ord a => a -> WBTree a -> WBTree a
delete k t = case t of
    Leaf -> Leaf
    Node _ l x r -> case compare k x of
        LT -> balanceL (delete k l) x r
        GT -> balanceR l x (delete k r)
        EQ -> glue l r

----------------------------------------------------------------

{-| Checking validity of a set.
-}

valid :: Ord a => WBTree a -> Bool
valid t = balanced t && ordered t && validsize t

balanced :: WBTree a -> Bool
balanced Leaf           = True
balanced (Node _ l _ r) = isBalanced l r && isBalanced r l
                       && balanced l     && balanced r

ordered :: Ord a => WBTree a -> Bool
ordered t = bounded (const True) (const True) t
  where
    bounded lo hi t' = case t' of
        Leaf         -> True
        Node _ l x r -> lo x && hi x && bounded lo (<x) l && bounded (>x) hi r

validsize :: WBTree a -> Bool
validsize t = realsize t == Just (size t)
  where
    realsize t' = case t' of
        Leaf            -> Just 0
        Node s l _ r -> case (realsize l,realsize r) of
            (Just n,Just m)  | n+m+1 == s -> Just s
            _                             -> Nothing

----------------------------------------------------------------

{-| Joining two sets with an element. O(log N)

    Each element of the left set must be less than the element.
    Each element of the right set must be greater than the element.
-}

join :: Ord a => WBTree a -> a -> WBTree a -> WBTree a
join Leaf x r   = insert x r
join l x Leaf   = insert x l
join l@(Node _ ll lx lr) x r@(Node _ rl rx rr)
  | bal1 && bal2 = node l x r
  | bal1         = balanceL ll lx (join lr x r)
  | otherwise    = balanceR (join l x rl) rx rr
  where
    bal1 = isBalanced l r
    bal2 = isBalanced r l

{-| Merging two sets. O(log N)

    Each element of the left set must be less than each element of
    the right set.
-}

merge :: WBTree a -> WBTree a -> WBTree a
merge Leaf r   = r
merge l Leaf   = l
merge l@(Node _ ll lx lr) r@(Node _ rl rx rr)
  | bal1 && bal2 = glue l r
  | bal1         = balanceL ll lx (merge lr r)
  | otherwise    = balanceR (merge l rl) rx rr
  where
    bal1 = isBalanced l r
    bal2 = isBalanced r l

glue :: WBTree a -> WBTree a -> WBTree a
glue Leaf r = r
glue l Leaf = l
glue l r
  | size l > size r = balanceL (deleteMax l) (maximum l) r
  | otherwise       = balanceR l (minimum r) (deleteMin r)

{-| Splitting a set. O(log N)

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

split :: Ord a => a -> WBTree a -> (WBTree a, WBTree a)
split _ Leaf           = (Leaf,Leaf)
split k (Node _ l x r) = case compare k x of
    LT -> let (lt,gt) = split k l in (lt,join gt x r)
    GT -> let (lt,gt) = split k r in (join l x lt,gt)
    EQ -> (l,r)

----------------------------------------------------------------

{-| Finding the minimum element. O(log N)

>>> minimum (fromList [3,5,1])
1
>>> minimum empty
*** Exception: minimum
-}

minimum :: WBTree a -> a
minimum (Node _ Leaf x _) = x
minimum (Node _ l _ _)    = minimum l
minimum _                 = error "minimum"

{-| Finding the maximum element. O(log N)

>>> maximum (fromList [3,5,1])
5
>>> maximum empty
*** Exception: maximum
-}

maximum :: WBTree a -> a
maximum (Node _ _ x Leaf) = x
maximum (Node _ _ _ r)    = maximum r
maximum _                 = error "maximum"

----------------------------------------------------------------

{-| Creating a union set from two sets. O(N + M)

>>> union (fromList [5,3]) (fromList [5,7]) == fromList [3,5,7]
True
-}

union :: Ord a => WBTree a -> WBTree a -> WBTree a
union t1 Leaf = t1
union Leaf t2 = t2
union t1 (Node _ l x r) = join (union l' l) x (union r' r)
  where
    (l',r') = split x t1

{-| Creating a intersection set from sets. O(N + N)

>>> intersection (fromList [5,3]) (fromList [5,7]) == singleton 5
True
-}

intersection :: Ord a => WBTree a -> WBTree a -> WBTree a
intersection Leaf _ = Leaf
intersection _ Leaf = Leaf
intersection t1 (Node _ l x r)
  | member x t1 = join (intersection l' l) x (intersection r' r)
  | otherwise   = merge (intersection l' l) (intersection r' r)
  where
    (l',r') = split x t1

{-| Creating a difference set from sets. O(N + N)

>>> difference (fromList [5,3]) (fromList [5,7]) == singleton 3
True
-}

difference :: Ord a => WBTree a -> WBTree a -> WBTree a
difference Leaf _  = Leaf
difference t1 Leaf = t1
difference t1 (Node _ l x r) = merge (difference l' l) (difference r' r)
  where
    (l',r') = split x t1

----------------------------------------------------------------

delta :: Int
delta = 3

gamma :: Int
gamma = 2

isBalanced :: WBTree a -> WBTree a -> Bool
isBalanced a b = delta * (size a + 1) >= (size b + 1)

isSingle :: WBTree a -> WBTree a -> Bool
isSingle a b = (size a + 1) < gamma * (size b + 1)

{- Adams's variant
isBalanced :: WBTree a -> WBTree a -> Bool
isBalanced a b = x + y <= 1 || delta * x >= y
  where x = size a
        y = size b

isSingle :: WBTree a -> WBTree a -> Bool
isSingle a b = size a < gamma * size b
-}
