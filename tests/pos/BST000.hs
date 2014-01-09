module BST () where

import Language.Haskell.Liquid.Prelude


{-@
data Bst [blen] k v <l :: root:k -> x1:k -> Prop, r :: root:k -> x1:k -> Prop>
  = Empty
  | Bind (key   :: k) 
         (value :: v) 
         (left  :: Bst <l, r> (k <l key>) v) 
         (right :: Bst <l, r> (k <r key>) v)
  @-}

{-@ measure blen :: (Bst k v) -> Int
    blen(Empty)        = 0
    blen(Bind k v l r) = 1 + (blen l) + (blen r)
  @-}

{-@ invariant {v:Bst k v | (blen v) >= 0} @-}

data Bst k v = Empty | Bind k v (Bst k v) (Bst k v)

{-@ type OBST k a = Bst <{\root v -> v < root }, {\root v ->  v > root}> k a @-}

{-@ chkMin :: (Ord k) => x:k -> OBST {v:k | x < v} a -> Bool @-}
chkMin :: (Ord k) => k -> Bst k a -> Bool
chkMin x Empty            = liquidAssertB True  
chkMin x (Bind k v lt rt) = liquidAssertB (x<k) && chkMin x lt && chkMin x rt

{-@
data Pair k v <p :: x0:k -> x1:k -> Prop, l :: x0:k -> x1:k -> Prop, r :: x0:k -> x1:k -> Prop>
  = P (fld0 :: k) (fld1 :: v) (tree :: Bst <l, r> (k <p fld0>) v) 
  @-}

data Pair k v = P k v (Bst k v)

getMin (Bind k v Empty rt) = (k, rt)
getMin (Bind k v lt rt)    = case getMin lt of
                               (k0, l') -> (k0, Bind k v l' rt) 
getMin _                   = error "getMin"

{-@ propMin :: (Ord k) => OBST k a -> Bool @-}
propMin :: (Ord k) => Bst k a -> Bool
propMin bst = chkMin x t
    where (x, t) = getMin bst 


zoo :: Int -> (Int, Int)
zoo x = (x, x + 1)


m = zoo 12












