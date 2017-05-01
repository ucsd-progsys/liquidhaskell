{-|
  Purely functional top-down splay sets.

   * D.D. Sleator and R.E. Rarjan,
     \"Self-Adjusting Binary Search Tree\",
     Journal of the Association for Computing Machinery,
     Vol 32, No 3, July 1985, pp 652-686.
     <http://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf>
-}

module Data.Set.Splay (
  -- * Data structures
    Splay(..), split
{-  -- * Creating sets
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
  , split
  , minimum
  , maximum
  , valid
  , (===)
  , showSet
  , printSet
-}  ) where

import Data.List (foldl')
import Prelude hiding (minimum, maximum, null)
import Language.Haskell.Liquid.Prelude

----------------------------------------------------------------

{-@ 
  data Splay a <l :: root:a -> a -> Bool, r :: root:a -> a -> Bool>
       = Node (value :: a) 
              (left  :: Splay <l, r> (a <l value>)) 
              (right :: Splay <l, r> (a <r value>)) 
       | Leaf 
@-}

data Splay a = Leaf | Node a (Splay a) (Splay a) deriving Show

{-@ type OSplay a = Splay <{v:a | v < root}, {v:a | v > root}> a @-}
{-
instance (Eq a) => Eq (Splay a) where
     t1 == t2 = toList t1 == toList t2

{-| Checking if two splay sets are exactly the same shape.
-}
(===) :: Eq a => Splay a -> Splay a -> Bool
Leaf            === Leaf            = True
(Node l1 x1 r1) === (Node l2 x2 r2) = x1 == x2 && l1 === l2 && r1 === r2
_               === _               = False
-}
----------------------------------------------------------------

{-| Splitting smaller and bigger with splay.
    Since this is a set implementation, members must be unique.
-}
{-@ split :: Ord a => a -> OSplay a -> (OSplay a, Bool, OSplay a) @-}

split :: Ord a => a -> Splay a -> (Splay a, Bool, Splay a)
split _ Leaf = (Leaf,False,Leaf)
split k x@(Node xk xl xr) = case compare k xk of
    EQ -> (xl, True, xr)
    GT -> case xr of
        Leaf -> (x, False, Leaf)
        Node yk yl yr -> case compare k yk of
            EQ ->     (Node xk xl yl, True, yr)           -- R  :zig
            GT -> let (lt, b, gt) = split k yr            -- RR :zig zag
                  in  (Node yk (Node xk xl yl) lt, b, gt)
            LT -> let (lt, b, gt) = split k yl
                  in  (Node xk xl lt, b, Node yk gt yr)   -- RL :zig zig
    LT -> case xl of
        Leaf          -> (Leaf, False, x)
        Node yk yl yr -> case compare k yk of
            EQ ->     (yl, True, Node xk yr xr)           -- L  :zig
            GT -> let (lt, b, gt) = split k yr            -- LR :zig zag
                  in  (Node yk yl lt, b, Node xk gt xr)
            LT -> let (lt, b, gt) = split k yl            -- LL :zig zig
                  in  (lt, b, Node yk gt (Node xk yr xr))

----------------------------------------------------------------
{-
{-| Empty set.
-}

empty :: Splay a
empty = Leaf

{-|
See if the splay set is empty.

>>> Data.Set.Splay.null empty
True
>>> Data.Set.Splay.null (singleton 1)
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

{-| Creating a list from a set.

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

member :: Ord a => a -> Splay a -> (Bool, Splay a)
member x t = case split x t of
    (l,True,r) -> (True, Node l x r)
    (Leaf,_,r) -> (False, r)
    (l,_,Leaf) -> (False, l)
    (l,_,r)    -> let (m,l') = deleteMax l
                  in (False, Node l' m r)

----------------------------------------------------------------

{-| Finding the minimum element.

>>> fst $ minimum (fromList [3,5,1])
1
>>> minimum empty
*** Exception: minimum
-}

minimum :: Splay a -> (a, Splay a)
minimum Leaf = error "minimum"
minimum t = let (x,mt) = deleteMin t in (x, Node Leaf x mt)

{-| Finding the maximum element.

>>> fst $ maximum (fromList [3,5,1])
5
>>> maximum empty
*** Exception: maximum
-}

maximum :: Splay a -> (a, Splay a)
maximum Leaf = error "maximum"
maximum t = let (x,mt) = deleteMax t in (x, Node mt x Leaf)

----------------------------------------------------------------

{-| Deleting the minimum element.

>>> snd (deleteMin (fromList [5,3,7])) == fromList [5,7]
True
>>> deleteMin empty
*** Exception: deleteMin
-}

deleteMin :: Splay a -> (a, Splay a)
deleteMin Leaf                          = error "deleteMin"
deleteMin (Node Leaf x r)               = (x,r)
deleteMin (Node (Node Leaf lx lr) x r)  = (lx, Node lr x r)
deleteMin (Node (Node ll lx lr) x r)    = let (k,mt) = deleteMin ll
                                          in (k, Node mt lx (Node lr x r))

{-| Deleting the maximum

>>> snd (deleteMax (fromList [(5,"a"), (3,"b"), (7,"c")])) == fromList [(3,"b"), (5,"a")]
True
>>> deleteMax empty
*** Exception: deleteMax
-}

deleteMax :: Splay a -> (a, Splay a)
deleteMax Leaf                          = error "deleteMax"
deleteMax (Node l x Leaf)               = (x,l)
deleteMax (Node l x (Node rl rx Leaf))  = (rx, Node l x rl)
deleteMax (Node l x (Node rl rx rr))    = let (k,mt) = deleteMax rr
                                          in (k, Node (Node l x rl) rx mt)

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
delete x t = case split x t of
    (l, True, r) -> union l r
    _            -> t

----------------------------------------------------------------

{-| Creating a union set from two sets.

>>> union (fromList [5,3]) (fromList [5,7]) == fromList [3,5,7]
True
-}

union :: Ord a => Splay a -> Splay a -> Splay a
union Leaf t = t
union (Node a x b) t = Node (union ta a) x (union tb b)
  where
    (ta,_,tb) = split x t

{-| Creating a intersection set from sets.

>>> intersection (fromList [5,3]) (fromList [5,7]) == singleton 5
True
-}

intersection :: Ord a => Splay a -> Splay a -> Splay a
intersection Leaf _          = Leaf
intersection _ Leaf          = Leaf
intersection t1 (Node l x r) = case split x t1 of
    (l', True,  r') -> Node (intersection l' l) x (intersection r' r)
    (l', False, r') -> union (intersection l' l) (intersection r' r)

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
-}
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
