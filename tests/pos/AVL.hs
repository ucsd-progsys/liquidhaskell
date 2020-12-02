{- Example of AVL trees by michaelbeaumont -}

module AVL (Tree, singleton, insert, ht, bFac) where

-- Basic functions
{-@ data Tree [ht] @-} 
data Tree a = Nil | Tree a (Tree a) (Tree a) deriving Show

{-@ measure ht @-}
{-@ ht :: Tree a -> Nat @-}
ht              :: Tree a -> Int
ht Nil          = 0
ht (Tree x l r) = if (ht l) > (ht r) then (1 + ht l) else (1 + ht r)


{-@ measure bFac @-}
bFac Nil          = 0
bFac (Tree v l r) = ht l - ht r

{-@ htDiff :: s:Tree a -> t: Tree a -> {v: Int | HtDiff s t v} @-}
htDiff :: Tree a -> Tree a -> Int
htDiff l r = ht l - ht r

{-@ emp :: {v: AVLTree | ht v == 0} @-}
emp = Nil

{-@ singleton :: a -> {v: AVLTree | ht v == 1 }@-}
singleton a = Tree a Nil Nil

-- | Insert functions

{-@ decrease insert 3 @-}
{-@ insert :: a -> s: AVLTree -> {t: AVLTree | EqHt t s || HtDiff t s 1 } @-}
insert :: (Ord a) => a -> Tree a -> Tree a
insert a Nil = singleton a
insert a t@(Tree v l r) = case compare a v of
    LT -> insL
    GT -> insR
    EQ -> t
    where r' = insert a r
          l' = insert a l
          insL | siblDiff > 1
                 && bFac l' == (0-1) = rebalanceLR v l' r
               | siblDiff > 1
                 && bFac l' == 1  = rebalanceLL v l' r
               | siblDiff <= 1 = Tree v l' r
               | otherwise = t
               where siblDiff = htDiff l' r
          insR | siblDiff > 1
                 && bFac r' == 1 = rebalanceRL v l r'
               | siblDiff > 1
                 && bFac r' == (0-1) = rebalanceRR v l r'
               | siblDiff <= 1 = Tree v l r'
               | otherwise = t
               where siblDiff = htDiff r' l

{-@ rebalanceLL :: a -> l:{AVLTree | LeftHeavy l } -> r:{AVLTree | HtDiff l r 2} -> {t:AVLTree | EqHt t l } @-}
rebalanceLL v (Tree lv ll lr) r                 = Tree lv ll (Tree v lr r)

{-@ rebalanceLR :: a -> l:{AVLTree | RightHeavy l } -> r:{AVLTree | HtDiff l r 2 } -> {t: AVLTree | EqHt t l } @-}
rebalanceLR v (Tree lv ll (Tree lrv lrl lrr)) r = Tree lrv (Tree lv ll lrl) (Tree v lrr r)

{-@ rebalanceRR :: a -> l: AVLTree -> r: {AVLTree | RightHeavy r && HtDiff r l 2 } -> {t: AVLTree | EqHt t r } @-}
rebalanceRR v l (Tree rv rl rr)                 = Tree rv (Tree v l rl) rr

{-@ rebalanceRL :: a -> l: AVLTree -> r:{AVLTree | LeftHeavy r && HtDiff r l 2} -> {t: AVLTree | EqHt t r } @-}
rebalanceRL v l (Tree rv (Tree rlv rll rlr) rr) = Tree rlv (Tree v l rll) (Tree rv rlr rr)

-- Test
main = do
    mapM_ print [a,b,c,d]
  where
    a = singleton 5
    b = insert 2 a
    c = insert 3 b
    d = insert 7 c

-- Liquid Haskell

{-@ predicate HtDiff S T D = (ht S) - (ht T) == D @-}
{-@ predicate EqHt S T = (ht S) == (ht T) @-}

{-@ predicate LeftHeavy T = bFac T == 1 @-}
{-@ predicate RightHeavy T = bFac T == -1 @-}

{-@ measure balanced @-}
balanced :: Tree a -> Bool
balanced Nil = True
balanced (Tree v l r) = ((ht l) <= (ht r) + 1)
                      && (ht r <= ht l + 1)
                      && (balanced l)
                      && (balanced r)

{-@ type AVLTree = {v: Tree a | balanced v} @-}
