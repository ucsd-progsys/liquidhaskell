{-|
  Purely functional bottom-up splay sets.

   * D.D. Sleator and R.E. Rarjan,
     \"Self-Adjusting Binary Search Tree\",
     Journal of the Association for Computing Machinery,
     Vol 32, No 3, July 1985, pp 652-686.
     <http://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf>
-}

module Data.Set.BUSplay (
  -- * Data structures
    Splay(..)
  -- * Creating sets
  , empty
  , singleton
  , insert
  , fromList
  -- * Converting a list
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
  , minimum
  , maximum
  , valid
  , (===)
  , showSet
  , printSet
  ) where

import Data.List (foldl')
import Prelude hiding (minimum, maximum, null)

----------------------------------------------------------------

data Splay a = Leaf | Node (Splay a) a (Splay a) deriving Show

instance (Eq a) => Eq (Splay a) where
    t1 == t2 = toList t1 == toList t2

{-| Checking if two splay sets are exactly the same shape.
-}
(===) :: Eq a => Splay a -> Splay a -> Bool
Leaf            === Leaf            = True
(Node l1 x1 r1) === (Node l2 x2 r2) = x1 == x2 && l1 === l2 && r1 === r2
_               === _               = False

data Direction a = L a (Splay a) | R a (Splay a) deriving Show

type Path a = [Direction a]

----------------------------------------------------------------

search :: Ord a => a -> Splay a -> (Splay a, Path a)
search k s = go s []
  where
    go Leaf           bs = (Leaf, bs)
    go t@(Node l x r) bs = case compare k x of
        LT -> go l (L x r : bs)
        GT -> go r (R x l : bs)
        EQ -> (t,bs)

searchMin :: Splay a -> (Splay a, Path a)
searchMin s = go s []
  where
    go Leaf         bs = (Leaf, bs)
    go (Node l x r) bs = go l (L x r : bs)

searchMax :: Splay a -> (Splay a, Path a)
searchMax s = go s []
  where
    go Leaf         bs = (Leaf, bs)
    go (Node l x r) bs = go r (R x l : bs)

----------------------------------------------------------------

splay :: Splay a -> Path a -> Splay a
splay t []                 = t
splay Leaf (L x r : bs)    = splay (Node Leaf x r) bs
splay Leaf (R x l : bs)    = splay (Node l x Leaf) bs
splay (Node a x b) [L y c] = Node a x (Node b y c) -- zig
splay (Node b y c) [R x a] = Node (Node a x b) y c -- zig
splay (Node a x b) (L y c : L z d : bs)
    = splay (Node a x (Node b y (Node c z d))) bs  -- zig zig
splay (Node b x c) (R y a : L z d : bs)
    = splay (Node (Node a y b) x (Node c z d)) bs  -- zig zag
splay (Node c z d) (R y b : R x a : bs)
    = splay (Node (Node (Node a x b) y c) z d) bs  -- zig zig
splay (Node b x c) (L y d : R z a : bs)
    = splay (Node (Node a z b) x (Node c y d)) bs  -- zig zag

----------------------------------------------------------------

{-| Empty set.
-}

empty :: Splay a
empty = Leaf

{-|
See if the splay set is empty.

>>> Data.Set.BUSplay.null empty
True
>>> Data.Set.BUSplay.null (singleton 1)
False
-}

null :: Splay a -> Bool
null Leaf = True
null _ = False

{-| Singleton set.
-}

singleton :: a -> Splay a
singleton x = Node Leaf x Leaf

----------------------------------------------------------------

{-| Insertion.

>>> insert 5 (fromList [5,3]) == fromList [3,5]
True
>>> insert 7 (fromList [5,3]) == fromList [3,5,7]
True
>>> insert 5 empty            == singleton 5
True
-}

insert :: Ord a => a -> Splay a -> Splay a
insert x t = Node l x r
  where
    (l,_,r) = split x t

----------------------------------------------------------------

{-| Creating a set from a list.

>>> empty == fromList []
True
>>> singleton 'a' == fromList ['a']
True
>>> fromList [5,3,5] == fromList [5,3]
True
-}

fromList :: Ord a => [a] -> Splay a
fromList = foldl' (flip insert) empty

----------------------------------------------------------------

{-| Creating a list from a set. O(N)

>>> toList (fromList [5,3])
[3,5]
>>> toList empty
[]
-}

toList :: Splay a -> [a]
toList t = inorder t []
  where
    inorder Leaf xs = xs
    inorder (Node l x r) xs = inorder l (x : inorder r xs)

----------------------------------------------------------------

{-| Checking if this element is a member of a set?

>>> fst $ member 5 (fromList [5,3])
True
>>> fst $ member 1 (fromList [5,3])
False
-}

-- this is 'access' in the paper
member :: Ord a => a -> Splay a -> (Bool, Splay a)
member x t = case search x t of
    (Leaf, []) -> (False, empty)
    (Leaf, ps) -> (False, splay Leaf ps)
    (s, ps)    -> (True,  splay s ps)

----------------------------------------------------------------

{-| Finding the minimum element.

>>> fst $ minimum (fromList [3,5,1])
1
>>> minimum empty
*** Exception: minimum
-}

minimum :: Splay a -> (a, Splay a)
minimum t = case uncurry splay $ searchMin t of
    Leaf          -> error "minimum"
    s@(Node _ x _) -> (x, s)

{-| Finding the maximum element.

>>> fst $ maximum (fromList [3,5,1])
5
>>> maximum empty
*** Exception: maximum
-}

maximum :: Splay a -> (a, Splay a)
maximum t = case uncurry splay $ searchMax t of
    Leaf           -> error "maximum"
    s@(Node _ x _) -> (x, s)

----------------------------------------------------------------

{-| Deleting the minimum element.

>>> deleteMin (fromList [5,3,7]) == fromList [5,7]
True
>>> deleteMin empty
*** Exception: deleteMin
-}

deleteMin :: Splay a -> Splay a
deleteMin Leaf = error "deleteMin"
deleteMin t = case minimum t of
    (_, Node Leaf _ r) -> r
    _                  -> error "deleteMin"

{-| Deleting the maximum

>>> deleteMax (fromList [(5,"a"), (3,"b"), (7,"c")]) == fromList [(3,"b"), (5,"a")]
True
>>> deleteMax empty
*** Exception: deleteMax
-}

deleteMax :: Splay a -> Splay a
deleteMax Leaf = error "deleteMax"
deleteMax t = case maximum t of
    (_, Node l _ Leaf) -> l
    _                  -> error "deleteMax"


----------------------------------------------------------------

{-| Deleting this element from a set.

>>> delete 5 (fromList [5,3]) == singleton 3
True
>>> delete 7 (fromList [5,3]) == fromList [3,5]
True
>>> delete 5 empty            == empty
True
-}

delete :: Ord a => a -> Splay a -> Splay a
delete _ Leaf = Leaf
delete x t = case member x t of
    (True,  Node l _ r) -> merge l r
    (False, s)          -> s
    _                   -> error "delete"

----------------------------------------------------------------

{-| Creating a union set from two sets.

>>> union (fromList [5,3]) (fromList [5,7]) == fromList [3,5,7]
True
-}

union :: Ord a => Splay a -> Splay a -> Splay a
union t1 Leaf = t1
union Leaf t2 = t2
union t1 (Node l x r) = Node (union l' l) x (union r' r)
  where
    (l',_,r') = split x t1

{-| Creating a intersection set from sets.

>>> intersection (fromList [5,3]) (fromList [5,7]) == singleton 5
True
-}

intersection :: Ord a => Splay a -> Splay a -> Splay a
intersection Leaf _ = Leaf
intersection _ Leaf = Leaf
intersection t1 (Node l x r) = case split x t1 of
    (l', True,  r') -> Node (intersection l' l) x (intersection r' r)
    (l', False, r') -> merge (intersection l' l) (intersection r' r)

{-| Creating a difference set from sets.

>>> difference (fromList [5,3]) (fromList [5,7]) == singleton 3
True
-}

difference :: Ord a => Splay a -> Splay a -> Splay a
difference Leaf _          = Leaf
difference t1 Leaf         = t1
difference t1 (Node l x r) = union (difference l' l) (difference r' r)
  where
    (l',_,r') = split x t1

----------------------------------------------------------------
-- Basic operations
----------------------------------------------------------------

merge :: Splay a -> Splay a -> Splay a
merge Leaf t2 = t2
merge t1 Leaf = t1
merge t1 t2 = Node l x t2
  where
    (_, Node l x Leaf) = maximum t1

split :: Ord a => a -> Splay a -> (Splay a, Bool, Splay a)
split _ Leaf = (Leaf,False,Leaf)
split x t    = case member x t of
    (True,   Node l _ r) -> (l,True,r)
    (False,  Node l y r) -> case compare x y of
        LT -> (l, False, Node Leaf y r)
        GT -> (Node l y Leaf, False, r)
        EQ -> error "split"
    _ -> error "split"

{-| Checking validity of a set.
-}

valid :: Ord a => Splay a -> Bool
valid t = isOrdered t

isOrdered :: Ord a => Splay a -> Bool
isOrdered t = ordered $ toList t
  where
    ordered [] = True
    ordered [_] = True
    ordered (x:y:xys) = x < y && ordered (y:xys)


showSet :: Show a => Splay a -> String
showSet = showSet' ""

showSet' :: Show a => String -> Splay a -> String
showSet' _ Leaf = "\n"
showSet' pref (Node l x r) = show x ++ "\n"
                        ++ pref ++ "+ " ++ showSet' pref' l
                        ++ pref ++ "+ " ++ showSet' pref' r
  where
    pref' = "  " ++ pref

printSet :: Show a => Splay a -> IO ()
printSet = putStr . showSet
