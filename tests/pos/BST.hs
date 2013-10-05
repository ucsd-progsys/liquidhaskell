module BST where

import Language.Haskell.Liquid.Prelude

{-@
data Bst [blen] k v <l :: x0:k -> x1:k -> Prop, r :: x0:k -> x1:k -> Prop>
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

{-@
data Pair k v <p :: x0:k -> x1:k -> Prop, l :: x0:k -> x1:k -> Prop, r :: x0:k -> x1:k -> Prop>
  = P (fld0 :: k) (fld1 :: v) (tree :: Bst <l, r> (k <p fld0>) v) 
  @-}

data Pair k v = P k v (Bst k v)

-- insert :: (Eq k, Ord k) => k -> v -> Bst k v -> Bst k v
insert k v Empty  = Bind k v Empty Empty
insert k v (Bind k' v' l r)
  | k == k'       = Bind k v l r
  | k < k'        = Bind k' v' (insert k v l) r
  | otherwise     = Bind k' v' l (insert k v r)

-- delete :: (Eq k, Ord k) => k -> Bst k v -> Bst k v
delete _ Empty = Empty
delete k' (Bind k v l r)
  | k' == k = 
      case r of 
       Empty   -> l
       _       -> let P kmin vmin r' = getMin r in Bind kmin vmin l r'
  | k' < k = Bind k v (delete k' l) r
  | otherwise = Bind k v l (delete k' r)

getMin (Bind k v Empty rt) = P k v rt
getMin (Bind k v lt rt)    = P k0min v0min (Bind k v l' rt)
   where P k0min v0min l' = getMin lt
getMin _                   = error "getMin"

chkMin x Empty            = liquidAssertB True  
chkMin x (Bind k v lt rt) = liquidAssertB (x<k) && chkMin x lt && chkMin x rt

chk Empty            = liquidAssertB True  
chk (Bind k v lt rt) = chk lt && chk rt && chkl k lt && chkr k rt
		
chkl k Empty = liquidAssertB True
chkl k (Bind kl _ _ _) = liquidAssertB (kl < k)

chkr k Empty = liquidAssertB True
chkr k (Bind kr _ _ _) = liquidAssertB (k < kr)

key, key1, val, val1 :: Int
key = choose 0
val = choose 1
key1 = choose 0
val1 = choose 1

bst = insert key val $ insert key1 val1 Empty

mkBst = foldl (\t (k, v) -> insert k v t) Empty

prop        = chk bst
prop1       = chk $ mkBst $ zip [1..] [1..]
propDelete  = chk $ delete 1 bst
propMin     = chkMin x t
    where pr  = getMin bst
          P x _ t = pr
