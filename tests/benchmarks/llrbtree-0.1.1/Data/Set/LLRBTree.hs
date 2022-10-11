{-|
  Purely functional left-leaning red-black trees.

   * Robert Sedgewick, \"Left-Leaning Red-Black Trees\",
     Data structures seminar at Dagstuhl, Feb 2008.
     <http://www.cs.princeton.edu/~rs/talks/LLRB/LLRB.pdf>

   * Robert Sedgewick, \"Left-Leaning Red-Black Trees\",
     Analysis of Algorithms meeting at Maresias, Apr 2008
     <http://www.cs.princeton.edu/~rs/talks/LLRB/RedBlack.pdf>
-}

module Data.Set.LLRBTree (
  -- * Data structures
    RBTree(..)
  , Color(..)
  , BlackHeight
  -- * Creating red-black trees
  , empty
  , insert
  , singleton
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

>>> Data.Set.LLRBTree.null empty
True
>>> Data.Set.LLRBTree.null (singleton 1)
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

isBlackLeftBlack :: RBTree a -> Bool
isBlackLeftBlack (Node B _ Leaf _ _)             = True
isBlackLeftBlack (Node B _ (Node B _ _ _ _) _ _) = True
isBlackLeftBlack _                               = False

isBlackLeftRed :: RBTree a -> Bool
isBlackLeftRed (Node B _ (Node R _ _ _ _) _ _) = True
isBlackLeftRed _                               = False

----------------------------------------------------------------
-- Basic operations
----------------------------------------------------------------

{-| Checking validity of a tree.
-}

valid :: Ord a => RBTree a -> Bool
valid t = isBalanced t && isLeftLean t && blackHeight t && isOrdered t

isLeftLean :: RBTree a -> Bool
isLeftLean Leaf = True
isLeftLean (Node B _ _ _ (Node R _ _ _ _)) = False -- right only and both!
isLeftLean (Node _ _ r _ l) = isLeftLean r && isLeftLean l

----------------------------------------------------------------

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
insert' kx t@(Node c h l x r) = case compare kx x of
    LT -> balanceL c h (insert' kx l) x r
    GT -> balanceR c h l x (insert' kx r)
    EQ -> t

balanceL :: Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceL B h (Node R _ ll@(Node R _ _ _ _) lx lr) x r =
    Node R (h+1) (turnB ll) lx (Node B h lr x r)
balanceL c h l x r = Node c h l x r

balanceR :: Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
balanceR B h l@(Node R _ _ _ _) x r@(Node R _ _ _ _) =
    Node R (h+1) (turnB l) x (turnB r)
-- x is Black since Red eliminated by the case above
-- x is either Node or Leaf
balanceR c h l x (Node R rh rl rx rr) = Node c h (Node R rh l x rl) rx rr
balanceR c h l x r = Node c h l x r

----------------------------------------------------------------

{-| Deleting the minimum element. O(log N)

>>> deleteMin (fromList [5,3,7]) == fromList [5,7]
True
>>> deleteMin empty == empty
True
-}

deleteMin :: RBTree a -> RBTree a
deleteMin Leaf = empty
deleteMin t = case deleteMin' (turnR t) of
    Leaf -> Leaf
    s    -> turnB s

{-
  This deleteMin' keeps an invariant: the target node is always red.

  If the left child of the minimum node is Leaf, the right child
  MUST be Leaf thanks to the invariants of LLRB.
-}

deleteMin' :: RBTree a -> RBTree a
deleteMin' (Node R _ Leaf _ Leaf) = Leaf -- deleting the minimum
deleteMin' t@(Node R h l x r)
  -- Red
  | isRed l      = Node R h (deleteMin' l) x r
  -- Black-Black
  | isBB && isBR = hardMin t
  | isBB         = balanceR B (h-1) (deleteMin' (turnR l)) x (turnR r)
  -- Black-Red
  | otherwise    = Node R h (Node B lh (deleteMin' ll) lx lr) x r -- ll is Red
  where
    isBB = isBlackLeftBlack l
    isBR = isBlackLeftRed r
    Node B lh ll lx lr = l -- to skip Black
deleteMin' _ = error "deleteMin'"

-- Simplified but not keeping the invariant.
{-
deleteMin' :: RBTree a -> RBTree a
deleteMin' (Node R _ Leaf _ Leaf) = Leaf
deleteMin' t@(Node R h l x r)
  | isBB && isBR = hardMin t
  | isBB         = balanceR B (h-1) (deleteMin' (turnR l)) x (turnR r)
  where
    isBB = isBlackLeftBlack l
    isBR = isBlackLeftRed r
deleteMin' (Node c h l x r) = Node c h (deleteMin' l) x r
deleteMin' _ = error "deleteMin'"
-}

{-
  The hardest case. See slide 61 of:
	http://www.cs.princeton.edu/~rs/talks/LLRB/RedBlack.pdf
-}

hardMin :: RBTree a -> RBTree a
hardMin (Node R h l x (Node B rh (Node R _ rll rlx rlr) rx rr))
    = Node R h (Node B rh (deleteMin' (turnR l)) x rll)
               rlx
               (Node B rh rlr rx rr)
hardMin _ = error "hardMin"

----------------------------------------------------------------

{-| Deleting the maximum

>>> deleteMax (fromList [(5,"a"), (3,"b"), (7,"c")]) == fromList [(3,"b"), (5,"a")]
True
>>> deleteMax empty == empty
True
-}

deleteMax :: RBTree a -> RBTree a
deleteMax Leaf = empty
deleteMax t = case deleteMax' (turnR t) of
    Leaf -> Leaf
    s    -> turnB s

{-
  This deleteMax' keeps an invariant: the target node is always red.

  If the right child of the minimum node is Leaf, the left child
  is:

  1) A Leaf -- we can delete it
  2) A red node -- we can rotateR it and have 1).
-}

deleteMax' :: RBTree a -> RBTree a
deleteMax' (Node R _ Leaf _ Leaf) = Leaf -- deleting the maximum
deleteMax' t@(Node R h l x r)
  | isRed l      = rotateR t
  -- Black-Black
  | isBB && isBR = hardMax t
  | isBB         = balanceR B (h-1) (turnR l) x (deleteMax' (turnR r))
  -- Black-Red
  | otherwise    = Node R h l x (rotateR r)
  where
    isBB = isBlackLeftBlack r
    isBR = isBlackLeftRed l
deleteMax' _ = error "deleteMax'"

-- Simplified but not keeping the invariant.
{-
deleteMax' :: RBTree a -> RBTree a
deleteMax' (Node R _ Leaf _ Leaf) = Leaf
deleteMax' t@(Node _ _ (Node R _ _ _ _) _ _) = rotateR t
deleteMax' t@(Node R h l x r)
  | isBB && isBR = hardMax t
  | isBB         = balanceR B (h-1) (turnR l) x (deleteMax' (turnR r))
  where
    isBB = isBlackLeftBlack r
    isBR = isBlackLeftRed l
deleteMax' (Node R h l x r) = Node R h l x (deleteMax' r)
deleteMax' _ = error "deleteMax'"
-}

{-
  rotateR ensures that the maximum node is in the form of (Node R Leaf _ Leaf).
-}

rotateR :: RBTree a -> RBTree a
rotateR (Node c h (Node R _ ll lx lr) x r) = balanceR c h ll lx (deleteMax' (Node R h lr x r))
rotateR _ = error "rorateR"

{-
  The hardest case. See slide 56 of:
	http://www.cs.princeton.edu/~rs/talks/LLRB/RedBlack.pdf
-}

hardMax :: RBTree a -> RBTree a
hardMax (Node R h (Node B lh ll@(Node R _ _ _ _ ) lx lr) x r)
    = Node R h (turnB ll) lx (balanceR B lh lr x (deleteMax' (turnR r)))
hardMax _              = error "hardMax"

----------------------------------------------------------------

{-| Deleting this element from a tree. O(log N)

>>> delete 5 (fromList [5,3]) == singleton 3
True
>>> delete 7 (fromList [5,3]) == fromList [3,5]
True
>>> delete 5 empty                         == empty
True
-}

delete :: Ord a => a -> RBTree a -> RBTree a
delete _ Leaf = empty
delete kx t = case delete' kx (turnR t) of
    Leaf -> Leaf
    t'   -> turnB t'

delete' :: Ord a => a -> RBTree a -> RBTree a
delete' _ Leaf = Leaf
delete' kx (Node c h l x r) = case compare kx x of
    LT -> deleteLT kx c h l x r
    GT -> deleteGT kx c h l x r
    EQ -> deleteEQ kx c h l x r

deleteLT :: Ord a => a -> Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
deleteLT kx R h l x r
  | isBB && isBR = Node R h (Node B rh (delete' kx (turnR l)) x rll) rlx (Node B rh rlr rx rr)
  | isBB         = balanceR B (h-1) (delete' kx (turnR l)) x (turnR r)
  where
    isBB = isBlackLeftBlack l
    isBR = isBlackLeftRed r
    Node B rh (Node R _ rll rlx rlr) rx rr = r
deleteLT kx c h l x r = Node c h (delete' kx l) x r

deleteGT :: Ord a => a -> Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
deleteGT kx c h (Node R _ ll lx lr) x r = balanceR c h ll lx (delete' kx (Node R h lr x r))
deleteGT kx R h l x r
  | isBB && isBR = Node R h (turnB ll) lx (balanceR B lh lr x (delete' kx (turnR r)))
  | isBB         = balanceR B (h-1) (turnR l) x (delete' kx (turnR r))
  where
    isBB = isBlackLeftBlack r
    isBR = isBlackLeftRed l
    Node B lh ll@(Node R _ _ _ _) lx lr = l
deleteGT kx R h l x r = Node R h l x (delete' kx r)
deleteGT _ _ _ _ _ _ = error "deleteGT"

deleteEQ :: Ord a => a -> Color -> BlackHeight -> RBTree a -> a -> RBTree a -> RBTree a
deleteEQ _ R _ Leaf _ Leaf = Leaf
deleteEQ kx c h (Node R _ ll lx lr) x r = balanceR c h ll lx (delete' kx (Node R h lr x r))
deleteEQ _ R h l _ r
  | isBB && isBR = balanceR R h (turnB ll) lx (balanceR B lh lr m (deleteMin' (turnR r)))
  | isBB         = balanceR B (h-1) (turnR l) m (deleteMin' (turnR r))
  where
    isBB = isBlackLeftBlack r
    isBR = isBlackLeftRed l
    Node B lh ll@(Node R _ _ _ _) lx lr = l
    m = minimum r
deleteEQ _ R h l _ r@(Node B rh rl rx rr) = Node R h l m (Node B rh (deleteMin' rl) rx rr) -- rl is Red
  where
    m = minimum r
deleteEQ _ _ _ _ _ _ = error "deleteEQ"

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
  | otherwise = Node B h (turnR t1) m t2'
  where
    m  = minimum t2
    t2' = deleteMin t2
    h2' = height t2'
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
    LT -> (lt, join gt x r) where (lt,gt) = split kx l
    GT -> (join l x lt, gt) where (lt,gt) = split kx r
    EQ -> (turnB' l, r)

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
