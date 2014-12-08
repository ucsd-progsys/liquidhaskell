module AVL  where
 
{-@ data Tree [ht] = Nil | Tree (x::Int) (l::Tree) (r::Tree) @-}
data Tree = Nil | Tree Int Tree Tree
 
{-@ measure height @-}
{-@ height :: t:Tree -> {v:Int | v = ht t}  @-}
height :: Tree -> Int
height Nil          = 0
height (Tree _ l r) = (if height l > height r then 1 + height l else 1 + height r)

{-@ invariant {v:Tree | 0 <= ht v} @-}

{-@ measure ht :: Tree -> Int
    ht (Nil)        = 0
    ht (Tree x l r) = (if (ht l) > (ht r) then (1 + ht l) else (1 + ht r))
  @-}

{-@ emp :: {v: AVLTree | ht v == 0 } @-}
emp = Nil

{-@ singleton :: Int -> {v: AVLTree | ht v == 1 } @-}
singleton a = Tree a Nil Nil
 
{-@ measure bFac :: Tree -> Int
    bFac (Nil) = 0
    bFac (Tree v l r) = (ht l - ht r)
  @-}

{-@ balFac :: t:Tree -> {v:Int | v = bFac t} @-}
balFac (Nil)        = 0
balFac (Tree _ l r) = (height l) - (height r)
 
{-@ measure leftHeavy1 :: Tree -> Prop
leftHeavy1 (Nil) = true
leftHeavy1 (Tree v l r) = (ht l) == (ht r) + 1
@-}
 
{-@ measure rightHeavy1 :: Tree -> Prop
rightHeavy1 (Nil) = true
rightHeavy1 (Tree v l r) = (ht r) == (ht l) + 1
@-}
 
{-@ predicate LeftHeavyN T N  = bFac T == N    @-}
{-@ predicate RightHeavyN T N = bFac T == -(N) @-}
 
{-@ measure balanced :: Tree -> Prop
balanced (Nil) = true
balanced (Tree v l r) = (ht l <= ht r + 1 && ht r <= ht l + 1 && balanced l && balanced r)
@-}
 
{-@ type AVLTree = {v: Tree | balanced v} @-}
 
{-@ rebalanceLL ::
 Int ->
 l:{AVLTree | LeftHeavyN l 1 } ->
 {r: AVLTree | ht l == ht r + 2} ->
 AVLTree @-}
rebalanceLL v (Tree lv ll lr) r = Tree lv ll (Tree v lr r)
 
llPos = rebalanceLL 1 (Tree 2 (Tree 3 Nil Nil) Nil) Nil
--llNeg = rebalanceLL 1 Nil Nil
 
{-@ rebalanceLR ::
 Int ->
 l:{AVLTree | RightHeavyN l 1 } ->
 r:{AVLTree | ht l == ht r + 2} ->
 AVLTree @-}
rebalanceLR v (Tree lv ll (Tree lrv lrl lrr)) r = Tree lrv (Tree lv ll lrl) (Tree v lrr r)
--rebalanceLL v (Tree lrv (Tree lv ll lrl) lrr) r
 
{-@ rebalanceRR ::
 Int ->
 l: AVLTree ->
 r: {AVLTree | RightHeavyN r 1 && ht r == ht l + 2} ->
 AVLTree @-}
rebalanceRR v l (Tree rv rl rr) = Tree rv (Tree v l rl) rr
 
{-@ rebalanceRL ::
 Int ->
 l: AVLTree ->
 r:{AVLTree | LeftHeavyN r 1 && ht r - ht l == 2} ->
 AVLTree @-}
rebalanceRL v l (Tree rv (Tree rlv rll rlr) rr) = Tree rlv (Tree v l rll) (Tree rv rlr rr) 
 
{-@ insert :: AVLTree -> Int -> AVLTree @-}
insert Nil a = singleton a
insert (Tree v l r) a 
    | a > v && (height r') - (height l) == 2 && balFac r' == 1
        = rebalanceRL v l r'
    where r' = insert r a
          l' = insert l a