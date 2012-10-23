module BST where

import Language.Haskell.Liquid.Prelude


{-@
data Bst k v <l :: root:k -> x1:k -> Bool, r :: root:k -> x1:k -> Bool>
  = Empty
  | Bind (key   :: k) 
         (value :: v) 
         (left  :: Bst <l, r> (k <l key>) v) 
         (right :: Bst <l, r> (k <r key>) v)
  @-}
data Bst k v = Empty | Bind k v (Bst k v) (Bst k v)

{-@ type OBST k a = Bst <{v:k | v < root }, {v:k | v > root}> k a @-}

{-@ chkMin :: (Ord k) => x:k -> OBST {v:k | x < v} a -> Bool @-}
chkMin :: (Ord k) => k -> Bst k a -> Bool
chkMin x Empty            = liquidAssertB True  
chkMin x (Bind k v lt rt) = liquidAssertB (x<k) && chkMin x lt && chkMin x rt

{-@
data Pair k v <p :: x0:k -> x1:k -> Bool, l :: x0:k -> x1:k -> Bool, r :: x0:k -> x1:k -> Bool>
  = P (fld0 :: k) (fld1 :: v) (tree :: Bst <l, r> (k <p fld0>) v) 
  @-}

data Pair k v = P k v (Bst k v)

getMin (Bind k v Empty rt) = P k v rt
getMin (Bind k v lt rt)    = P k0min v0min (Bind k v l' rt)
   where P k0min v0min l' = getMin lt
   
{-@ propMin :: (Ord k) => OBST k a -> Bool @-}
propMin :: (Ord k) => Bst k a -> Bool
propMin bst = chkMin x t
    where pr  = getMin bst 
          P x _ t = pr



