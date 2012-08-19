module Map where

import Language.Haskell.Liquid.Prelude

-- LIQUID: There is some bizarre interaction between the names in Map-pred
-- and Pair-pred -- because the error goes away if you remove "Pair"
-- altogether from the code.

{-@ 
  data Map k a <l :: x00:k -> x1:k -> Bool, r :: x00:k -> x1:k -> Bool>
      = Tip 
      | Bin (sz    :: Size) 
            (key   :: k) 
            (value :: a) 
            (left  :: Map <l, r> (k <l key>) a) 
            (right :: Map <l, r> (k <r key>) a) 
  @-}

{-@ type OMap k a = Map <{v:k | v < x00 }, {v:k | v > x00}> k a @-}

data Map k a = Tip
             | Bin Size k a (Map k a) (Map k a)

type Size    = Int
{-@
data Pair k v <p :: x0:k -> x1:k -> Bool, l :: x0:k -> x1:k -> Bool, r :: x0:k -> x1:k -> Bool>
  = P (fld0 :: k) (fld1 :: v) (tree :: Map <l, r> (k <p fld0>) v) 
  @-}
data Pair k v = P k v (Map k v)

{-@ singleton :: k -> a -> OMap k a @-}
singleton :: k -> a -> Map k a
singleton k x
  = Bin 1 k x Tip Tip

{-@ insert :: Ord k => k -> a -> OMap k a -> OMap k a @-}
insert :: Ord k => k -> a -> Map k a -> Map k a
insert kx x t
  = case t of 
     Tip -> singleton kx x
     Bin sz ky y l r
         -> case compare kx ky of
              LT -> balance ky y (insert kx x l) r
              GT -> balance ky y l (insert kx x r)
              EQ -> Bin sz kx x l r

{-@ delete :: (Ord k) => k -> OMap k a -> OMap k a @-}
delete :: Ord k => k -> Map k a -> Map k a
delete k t 
  = case t of 
      Tip -> Tip
      Bin _ kx x l r
          -> case compare k kx of 
               LT -> balance kx x (delete k l) r
               GT -> balance kx x l (delete k r)
               EQ -> glue kx l r 


glue :: k -> Map k a -> Map k a -> Map k a
glue k Tip r = r
glue k l Tip = l
glue k l r
  | size l > size r = let P km1 vm lm = deleteFindMax l in balance km1 vm lm r
  | otherwise       = let P km2 vm rm = deleteFindMin r in balance km2 vm l rm

deleteFindMax :: Map k a -> Pair k a
deleteFindMax t 
  = case t of
      Bin _ k x l Tip -> P k x l
      Bin _ k x l r -> let P km3 vm rm = deleteFindMax r in P km3 vm (balance k x l rm) 
      Tip             -> P (error ms) (error ms) Tip
  where ms = "Map.deleteFindMax : can not return the maximal element of an empty Map"   


deleteFindMin :: Map k a -> Pair k a
deleteFindMin t 
  = case t of
      Bin _ k x Tip r -> P k x r
      Bin _ k x l r -> let P km4 vm lm = deleteFindMin l in P km4 vm (balance k x lm r) 
      Tip             -> P (error ms) (error ms) Tip
  where ms = "Map.deleteFindMin : can not return the maximal element of an empty Map"   


-------------------------------------------------------------------------------
--------------------------------- BALANCE -------------------------------------
-------------------------------------------------------------------------------

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


chkDel x Tip                = liquidAssertB True  
chkDel x (Bin sz k v lt rt) = liquidAssertB (not (x == k)) && chkDel x lt && chkDel x rt

chkMin x Tip                = liquidAssertB True  
chkMin x (Bin sz k v lt rt) = liquidAssertB (x<k) && chkMin x lt && chkMin x rt

chk Tip               = liquidAssertB True  
chk (Bin s k v lt rt) = chk lt && chk rt && chkl k lt && chkr k rt
		
chkl k Tip              = liquidAssertB True
chkl k (Bin _ kl _ _ _) = liquidAssertB (kl < k)

chkr k Tip              = liquidAssertB True
chkr k (Bin _ kr _ _ _) = liquidAssertB (k < kr)

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

propDelete  = chk $ delete x bst
   where x = choose 0
