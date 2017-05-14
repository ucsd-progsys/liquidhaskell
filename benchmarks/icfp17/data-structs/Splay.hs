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
  , split
  , minimum
  , maximum
  , valid
  , (===)
  , showSet
  , printSet
  ) where

import Data.List (foldl')
import Prelude hiding (minimum, maximum, null)
import Language.Haskell.Liquid.Prelude

----------------------------------------------------------------

-- LIQUID left depends on value, so their order had to be changed
{-@ data Splay [slen] a <l :: root:a -> a -> Prop, r :: root:a -> a -> Prop>
         = Node (value :: a) 
                (left  :: Splay <l, r> (a <l value>)) 
                (right :: Splay <l, r> (a <r value>)) 
         | Leaf 
@-}

{-@ measure slen :: (Splay a) -> Int
    slen(Leaf) = 0
    slen(Node v l r) = 1 + (slen l) + (slen r)
  @-}

{-@ slen :: s:Splay s -> {v:Nat | v = (slen s)} @-}
slen :: Splay a -> Int
slen (Leaf)       = 0
slen (Node v l r) = 1 + (slen l) + (slen r)

{-@ type SumSLen A B = {v:Nat | v = (slen A) + (slen B)} @-}

{-@ invariant {v:Splay a | (slen v) >= 0} @-}

data Splay a = Leaf | Node a (Splay a) (Splay a) deriving Show

{-@ type OSplay a = Splay <{\root v -> v < root}, {\root v -> v > root}> a @-}

{-@ type OSplayLE a S = {v:OSplay a | (slen v) <= (slen S)}  @-}

{-@ type MinSPair   a = (a, OSplay a) <\fld -> {v : Splay {v:a|v>fld} | 0=0}> @-}
{-@ type MinEqSPair a = (a, OSplay a) <\fld -> {v : Splay {v:a|v>=fld}| 0=0}> @-}

{-@ type MaxSPair   a = (a, OSplay a) <\fld -> {v : Splay {v:a|v<fld} | 0=0}> @-}
{-@ type MaxEqSPair a = (a, OSplay a) <\fld -> {v : Splay {v:a|v<=fld}| 0=0}> @-}

instance (Eq a) => Eq (Splay a) where
    t1 == t2 = toList t1 == toList t2

{-| Checking if two splay sets are exactly the same shape.
-}
(===) :: Eq a => Splay a -> Splay a -> Bool
Leaf            === Leaf            = True
(Node x1 l1 r1) === (Node x2 l2 r2) = x1 == x2 && l1 === l2 && r1 === r2
_               === _               = False

----------------------------------------------------------------

{-| Splitting smaller and bigger with splay.
    Since this is a set implementation, members must be unique.
-}

{-@ split :: Ord a => x:a -> s:OSplay a
          -> (OSplayLE {v:a | v<x} s, Bool, OSplayLE {v:a | v>x} s)
  @-}

split :: Ord a => a -> Splay a -> (Splay a, Bool, Splay a)
split _ Leaf = (Leaf,False,Leaf)
split k (Node xk xl xr) = case compare k xk of
    EQ -> (xl, True, xr)
    GT -> case xr of
        Leaf -> (Node xk xl Leaf, False, Leaf)
        Node yk yl yr -> case compare k yk of
            EQ ->     (Node xk xl yl, True, yr)           -- R  :zig
            GT -> let (lt, b, gt) = split k yr            -- RR :zig zag
                  in  (Node yk (Node xk xl yl) lt, b, gt)
            LT -> let (lt, b, gt) = split k yl
                  in  (Node xk xl lt, b, Node yk gt yr)   -- RL :zig zig
    LT -> case xl of
        Leaf          -> (Leaf, False, Node xk Leaf xr)
        Node yk yl yr -> case compare k yk of
            EQ ->     (yl, True, Node xk yr xr)           -- L  :zig
            GT -> let (lt, b, gt) = split k yr            -- LR :zig zag
                  in  (Node yk yl lt, b, Node xk gt xr)
            LT -> let (lt, b, gt) = split k yl            -- LL :zig zig
                  in  (lt, b, Node yk gt (Node xk yr xr))

----------------------------------------------------------------
{-| Empty set.
-}

{-@ empty :: OSplay a @-}
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

{-@ singleton :: a -> OSplay a @-}
singleton :: a -> Splay a
singleton x = Node x Leaf Leaf

----------------------------------------------------------------

{-| Insertion.

>>> insert 5 (fromList [5,3]) == fromList [3,5]
True
>>> insert 7 (fromList [5,3]) == fromList [3,5,7]
True
>>> insert 5 empty            == singleton 5
True
-}

{-@ insert :: Ord a => a -> OSplay a -> OSplay a @-}
insert :: Ord a => a -> Splay a -> Splay a
insert x t = Node x l r
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

{-@ fromList :: Ord a => [a] -> OSplay a @-}
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
    inorder (Node x l r) xs = inorder l (x : inorder r xs)

----------------------------------------------------------------
{-| Checking if this element is a member of a set?

>>> fst $ member 5 (fromList [5,3])
True
>>> fst $ member 1 (fromList [5,3])
False
-}

{-@ member :: Ord a => a -> OSplay a -> (Bool, OSplay a) @-}
member :: Ord a => a -> Splay a -> (Bool, Splay a)
member x t = case split x t of
    (l,True,r) -> (True, Node x l r)
    (Leaf,_,r) -> (False, r)
    (l,_,Leaf) -> (False, l)
    (l,_,r)    -> let (m,l') = deleteMax l
                  in (False, Node m l' r)

----------------------------------------------------------------

{-| Finding the minimum element.

>>> fst $ minimum (fromList [3,5,1])
1
>>> minimum empty
*** Exception: minimum
-}

{-@ minimum :: OSplay a -> MinEqSPair a @-}
minimum :: Splay a -> (a, Splay a)
minimum Leaf = error "minimum"
minimum t = let (x,mt) = deleteMin t in (x, Node x Leaf mt)

{-| Finding the maximum element.

>>> fst $ maximum (fromList [3,5,1])
5
>>> maximum empty
*** Exception: maximum
-}

{-@ maximum :: OSplay a -> MaxEqSPair a @-}
maximum :: Splay a -> (a, Splay a)
maximum Leaf = error "maximum"
maximum t = let (x,mt) = deleteMax t in (x, Node x mt Leaf)

----------------------------------------------------------------

{-| Deleting the minimum element.

>>> snd (deleteMin (fromList [5,3,7])) == fromList [5,7]
True
>>> deleteMin empty
*** Exception: deleteMin
-}

{-@ deleteMin :: OSplay a -> MinSPair a @-}
deleteMin :: Splay a -> (a, Splay a)
deleteMin Leaf                          = error "deleteMin"
deleteMin (Node x Leaf r)               = (x,r)
deleteMin (Node x (Node lx Leaf lr) r)  = (lx, Node x lr r)
deleteMin (Node x (Node lx ll lr) r)    = let (k,mt) = deleteMin ll
                                          in (k, Node lx mt (Node x lr r))

{-| Deleting the maximum

>>> snd (deleteMax (fromList [(5,"a"), (3,"b"), (7,"c")])) == fromList [(3,"b"), (5,"a")]
True
>>> deleteMax empty
*** Exception: deleteMax
-}


{-@ deleteMax :: OSplay a -> MaxSPair a @-}
deleteMax :: Splay a -> (,) a (Splay a)
deleteMax Leaf                          = error "deleteMax"
deleteMax (Node x l Leaf)               = (x,l)
deleteMax (Node x l (Node rx rl Leaf))  = (rx, Node x l rl)
deleteMax (Node x l (Node rx rl rr))    = let (k,mt) = deleteMax rr
                                          in (k, Node rx (Node x l rl) mt)
----------------------------------------------------------------

{-| Deleting this element from a set.

>>> delete 5 (fromList [5,3]) == singleton 3
True
>>> delete 7 (fromList [5,3]) == fromList [3,5]
True
>>> delete 5 empty            == empty
True
-}

-- Liquid TOPROVE
--  delete :: Ord a => x:a -> OSplay a -> OSplay {v:a| v!=x}
{-@ delete :: Ord a => x:a -> OSplay a -> OSplay a @-}
delete :: Ord a => a -> Splay a -> Splay a
delete x t = case split x t of
    (l, True, r) -> union l r
    _            -> t

----------------------------------------------------------------

{-| Creating a union set from two sets.

>>> union (fromList [5,3]) (fromList [5,7]) == fromList [3,5,7]
True
-}

{-@ union :: Ord a => OSplay a -> OSplay a -> OSplay a@-}
union :: Ord a => Splay a -> Splay a -> Splay a
union a b = unionT a b (slen a + slen b)
--LIQUID union Leaf t = t
--LIQUID union (Node x a b) t = Node x (union ta a) (union tb b)
--LIQUID   where
--LIQUID     (ta,_,tb) = split x t

{-@ unionT :: Ord a => a:OSplay a -> b:OSplay a -> SumSLen a b -> OSplay a @-}
{-@ Decrease unionT 4 @-}
{- LIQUID WITNESS -}
unionT :: Ord a => Splay a -> Splay a -> Int -> Splay a
unionT Leaf         t _ = t
unionT (Node x a b) t _ = Node x (unionT ta a (slen ta + slen a))
                                 (unionT tb b (slen tb + slen b))
  where
    (ta,_,tb) = split x t


{-| Creating a intersection set from sets.

>>> intersection (fromList [5,3]) (fromList [5,7]) == singleton 5
True
-}

{-@ intersection :: Ord a => OSplay a -> OSplay a -> OSplay a @-}
intersection :: Ord a => Splay a -> Splay a -> Splay a
intersection a b = intersectionT a b (slen a + slen b)
--LIQUID intersection Leaf _          = Leaf
--LIQUID intersection _ Leaf          = Leaf
--LIQUID intersection t1 (Node x l r) = case split x t1 of
--LIQUID     (l', True,  r') -> Node x (intersection l' l) (intersection r' r)
--LIQUID     (l', False, r') -> union (intersection l' l) (intersection r' r)

{-@ intersectionT :: Ord a => a:OSplay a -> b:OSplay a -> SumSLen a b -> OSplay a @-}
{-@ Decrease intersectionT 4 @-}
{- LIQUID WITNESS -}
intersectionT :: Ord a => Splay a -> Splay a -> Int -> Splay a
intersectionT Leaf _          _ = Leaf
intersectionT _ Leaf          _ = Leaf
intersectionT t1 (Node x l r) _ = case split x t1 of
    (l', True,  r') -> Node x (intersectionT l' l (slen l' + slen l))
                              (intersectionT r' r (slen r' + slen r))
    (l', False, r') -> union (intersectionT l' l (slen l' + slen l))
                             (intersectionT r' r (slen r' + slen r))

{-| Creating a difference set from sets.

>>> difference (fromList [5,3]) (fromList [5,7]) == singleton 3
True
-}

{-@ difference :: Ord a => OSplay a -> OSplay a -> OSplay a @-}
difference :: Ord a => Splay a -> Splay a -> Splay a
difference a b = differenceT a b (slen a + slen b)
--LIQUID difference Leaf _          = Leaf
--LIQUID difference t1 Leaf         = t1
--LIQUID difference t1 (Node x l r) = union (difference l' l) (difference r' r)
--LIQUID   where
--LIQUID     (l',_,r') = split x t1

{-@ differenceT :: Ord a => a:OSplay a -> b:OSplay a -> SumSLen a b -> OSplay a @-}
{-@ Decrease differenceT 4 @-}
{- LIQUID WITNESS -}
differenceT :: Ord a => Splay a -> Splay a -> Int -> Splay a
differenceT Leaf _          _ = Leaf
differenceT t1 Leaf         _ = t1
differenceT t1 (Node x l r) _ = union (differenceT l' l (slen l' + slen l))
                                      (differenceT r' r (slen r' + slen r))
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
showSet = showSet_go ""

--LIQUID FIXME: renamed from `showSet'`, must fix parser!

{-@ Decrease showSet_go 3 @-}
showSet_go :: Show a => String -> Splay a -> String
showSet_go _ Leaf = "\n"
showSet_go pref (Node x l r) = show x ++ "\n"
                        ++ pref ++ "+ " ++ showSet_go pref' l
                        ++ pref ++ "+ " ++ showSet_go pref' r
  where
    pref' = "  " ++ pref

printSet :: Show a => Splay a -> IO ()
printSet = putStr . showSet

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
