module Map where

import Language.Haskell.Liquid.Prelude


data Map k a = Tip
             | Bin Size k a (Map k a) (Map k a)

type Size    = Int

data Pair k v = P k v (Map k v)


singleton :: k -> a -> Map k a
singleton k x
  = Bin 1 k x Tip Tip

insert :: Ord k => k -> a -> Map k a -> Map k a
insert kx x Tip  = singleton kx x
insert kx x (Bin sz ky y l r)
  | kx == ky   = Bin sz kx x l r
  | kx < ky    = balance ky y (insert kx x l) r
  | otherwise  = balance ky y l (insert kx x r)

-- fix Eq case 
-- can I use glue function?
delete :: Ord k => k -> Map k a -> Map k a
delete _ Tip = Tip
delete k (Bin _ kx x l r)
  | k == kx = 
      case r of 
       Tip   -> l
       _       -> let P kmin vmin r' = getMin r in balance kmin vmin l r'
  | k < kx    = balance kx x (delete k l) r
  | otherwise = balance kx x l (delete k r)

getMin (Bin sz k v Tip rt) = P k v rt
getMin (Bin sz k v lt rt)    = P k0min v0min (Bin (sz-1) k v l' rt)
   where P k0min v0min l' = getMin lt


delta, ratio :: Int
delta = 5
ratio = 2

balance :: k -> a -> Map k a -> Map k a -> Map k a 
balance k x l r 
  | sizeL + sizeR <= 1   = Bin sizeX k x l r
  | sizeR >= delta*sizeL = rotateL k x l r
  | sizeL >= delta*sizeR = rotateR k x l r
  | otherwise            = Bin sizeX k x l r
  where sizeL = size l
        sizeR = size r
        sizeX = sizeL + sizeR + 1

-- rotate
rotateL :: a -> b -> Map a b -> Map a b -> Map a b
rotateL k x l r@(Bin _ _ _ ly ry) 
  | size ly < ratio*size ry  = singleL k x l r
  | otherwise                = doubleL k x l r
rotateL _ _ _ Tip = error "rotateL Tip"

rotateR :: a -> b -> Map a b -> Map a b -> Map a b
rotateR k x l@(Bin _ _ _ ly ry) r
  | size ry < ratio*size ly  = singleR k x l r
  | otherwise                = doubleR k x l r
rotateR _ _ _ Tip = error "rotateR Tip"

-- basic rotations
singleL, singleR :: a -> b -> Map a b -> Map a b -> Map a b
singleL k1 x1 t1 (Bin _ k2 x2 t2 t3) = bin k2 x2 (bin k1 x1 t1 t2) t3
singleL _  _  _ Tip = error "sinlgeL Tip"
singleR k1 x1 (Bin _ k2 x2 t1 t2) t3 = Bin 0 k2 x2 t1 (Bin 0 k1 x1 t2 t3)
singleR _  _  _ Tip = error "sinlgeR Tip"

doubleL, doubleR :: a -> b -> Map a b -> Map a b -> Map a b
doubleL k1 x1 t1 (Bin _ k2 x2 (Bin _ k3 x3 t2 t3) t4)
 =bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)
doubleL _ _ _ _ = error "doubleL" 
doubleR k1 x1 (Bin _ k2 x2 t1 (Bin _ k3 x3 t2 t3)) t4 
  = bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)
doubleR _ _ _ _ = error "doubleR" 

bin :: k -> a -> Map k a -> Map k a -> Map k a
bin k x l r 
  = Bin (size l + size r + 1) k x l r

size :: Map k a -> Int
size t 
  = case t of 
      Tip            -> 0
      Bin sz _ _ _ _ -> sz


chkMin x Tip             = assert True  
chkMin x (Bin sz k v lt rt) = assert (x<k) && chkMin x lt && chkMin x rt

chk Tip               = assert True  
chk (Bin s k v lt rt) = chk lt && chk rt && chkl k lt && chkr k rt
		
chkl k Tip              = assert True
chkl k (Bin _ kl _ _ _) = assert (kl < k)

chkr k Tip              = assert True
chkr k (Bin _ kr _ _ _) = assert (k < kr)

key, key1, val, val1 :: Int
key = choose 0
val = choose 1
key1 = choose 0
val1 = choose 1

bst1 = insert key val Tip
bst  = insert key val $ insert key1 val1 Tip

mkBst = foldl (\t (k, v) -> insert k v t) Tip

prop        = chk bst1
prop1       = chk $ mkBst $ zip [1..] [1..]

propDelete  = chk $ delete 1 bst
propMin     = chkMin x t
    where pr  = getMin bst
          P x _ t = pr
