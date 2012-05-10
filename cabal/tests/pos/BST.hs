module BST where

import Language.Haskell.Liquid.Prelude


data Bst k v = Empty | Bind k v (Bst k v) (Bst k v)
data Pair k v = P k v (Bst k v)

-- type signature should be there, otherwise games in Rec
insert :: (Eq k, Ord k) => k -> v -> Bst k v -> Bst k v
insert k v Empty  = Bind k v Empty Empty
insert k v (Bind k' v' l r)
  | k == k' = Bind k v l r
  | k < k'  = let lt = insert k v l in Bind k' v' lt r
  | otherwise = Bind k' v' l (insert k v r)

delete :: (Eq k, Ord k) => k -> Bst k v -> Bst k v
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

chkMin x Empty            = assert True  
chkMin x (Bind k v lt rt) = assert (x<k) && chkMin x lt && chkMin x rt

chk Empty            = assert True  
chk (Bind k v lt rt) = chk lt && chk rt && chkl k lt && chkr k rt
		
chkl k Empty = assert True
chkl k (Bind kl _ _ _) = assert (kl < k)

chkr k Empty = assert True
chkr k (Bind kr _ _ _) = assert (k < kr)

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



















































































