module RedBlack where

----------------------------------------------------------------------------------- 
-- From: http://www.mew.org/~kazu/proj/red-black-tree/ ----------------------------
----------------------------------------------------------------------------------- 

data RBTree a = Leaf | Fork Color (RBTree a) a (RBTree a)
data Color    = Red  | Black

{-@
inline measure cheight :: Color -> Int
cheight (x) = if (x == Black) then 1 else 0
@-}

{-@ 
measure height        :: RBTree a -> Int   
height (Leaf)         = 0
height (Fork c l x r) = (cheight c) + (height l)
@-}

{-@ 
measure color        :: RBTree a -> Color 
color (Leaf)         = Black
color (Fork c l x r) = c
@-}

{-@ predicate isBlack X     = (X == Black)                                                 @-}
{-@ predicate isRed X       = (X == Red)                                                   @-}
{-@ predicate okRoot1 C L R = ((isRed C)  => ((isBlack (color L)) || (isBlack (color R)))) @-}
{-@ predicate okRoot2 C L R = ((isRed C)  => ((isBlack (color L)) && (isBlack (color R)))) @-}
{-@ predicate eqHeight  L R = ((height L) == (height R))                                   @-}

{-@ 
measure invKids2        :: RBTree a -> Prop 
invKids2 (Leaf)         =  true
invKids2 (Fork c l x r) =  (OkRoot2 c l r) && (invKids2 l) && (invKids2 r) 
@-}

{-@ 
measure invKids1        :: RBTree a -> Prop 
invKids1 (Leaf)         = true
invKids1 (Fork c l x r) = (OkRoot1 c l r) && (invKids2 l) && (invKids2 r)
@-}

{-@ 
measure invHeight        :: RBTree a -> Prop 
invHeight (Leaf)         =  true
invHeight (Fork c l x r) =  (eqHeight l r) && (invHeight l) && (invHeight r)
@-}

{-@ type RB1Tree a = {v: (RBTree a) | (invKids1 v) && (invHeight v)} @-}
{-@ type RB2Tree a = {v: (RBTree a) | (invKids2 v) && (invHeight v)} @-}

----------------------------------------------------------------------------------- 

{-@ empty :: IRBTree a @-}
empty     = Leaf

{-@ insert       :: Ord a => a -> RB2Tree a -> RB2Tree a @-}
insert x t       = Fork Black d e f
  where
    Fork _ d e f = ins x t

ins x Leaf             = Fork R Leaf x Leaf
ins x t@(Fork c l y r) = case compare x y of
                           LT -> balanceL c (ins x l) y r
                           GT -> balanceR c l y (ins x r)
                           EQ -> t

{-@ balanceL :: c:Color 
             -> l:(RB1Tree a) 
             -> x:a 
             -> r:{v : (RB2Tree a) | (eqHeight l v)} 
             -> {v:(RB2Tree a) | (height v) = (cheight c) + (height l) } @-}
balanceL :: Color -> RBTree a -> a -> RBTree a -> RBTree a
balanceL B (Fork R (Fork R a x b) y c) z d = Fork R (Fork B a x b) y (Fork B c z d)
balanceL B (Fork R a x (Fork R b y c)) z d = Fork R (Fork B a x b) y (Fork B c z d)
balanceL k a x b                           = Fork k a x b

{-@ balanceR :: c:Color 
             -> l:(RB2Tree a) 
             -> x:a 
             -> r:{v : (RB1Tree a) | (eqHeight l v)} 
             -> {v:(RB2Tree a) | (height v) = (cheight c) + (height l) } @-}
balanceR :: Color -> RBTree a -> a -> RBTree a -> RBTree a
balanceR B a x (Fork R b y (Fork R c z d)) = Fork R (Fork B a x b) y (Fork B c z d)
balanceR B a x (Fork R (Fork R b y c) z d) = Fork R (Fork B a x b) y (Fork B c z d)
balanceR k a x b                           = Fork k a x b


