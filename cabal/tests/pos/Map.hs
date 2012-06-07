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
insert kx x t
  = case t of 
     Tip -> singleton kx x
     Bin sz ky y l r
         -> case compare kx ky of
              LT -> balance ky y (insert kx x l) r
              GT -> balance ky y l (insert kx x r)
              EQ -> Bin sz kx x l r

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
  | size l > size r = let P km vm lm = deleteFindMax l in balance km vm lm r
  | otherwise       = let P km vm rm = deleteFindMin r in balance km vm l rm

deleteFindMax :: Map k a -> Pair k a
deleteFindMax t 
  = case t of
      Bin _ k x l Tip -> P k x l
      Bin _ k x l r -> let P km vm rm = deleteFindMax r in P km vm (balance k x l rm) 
      Tip             -> P (error ms) (error ms) Tip
  where ms = "Map.deleteFindMax : can not return the maximal element of an empty Map"   


deleteFindMin :: Map k a -> Pair k a
deleteFindMin t 
  = case t of
      Bin _ k x Tip r -> P k x r
      Bin _ k x l r -> let P km vm lm = deleteFindMin l in P km vm (balance k x lm r) 
      Tip             -> P (error ms) (error ms) Tip
  where ms = "Map.deleteFindMin : can not return the maximal element of an empty Map"   

alter :: Ord k => (Maybe a -> Maybe a) -> k -> Map k a -> Map k a
alter f k t 
  = case t of 
      Tip -> case f Nothing of
               Nothing -> Tip
               Just x  -> singleton k x
      Bin sx kx x l r 
          -> case compare k kx of
               LT -> balance kx x (alter f k l) r
               GT -> balance kx x l (alter f k r)
               EQ -> case f (Just x) of
                       Just x' -> Bin sx kx x' l r
                       Nothing -> glue kx l r
         
deleteMin :: Map k a -> Map k a
deleteMin (Bin _ _ _ Tip r) = r
deleteMin (Bin _ kx x l r)  = balance kx x (deleteMin l) r
deleteMin Tip               = Tip

deleteMax :: Map k a -> Map k a
deleteMax (Bin _ _ _ l Tip) = l
deleteMax (Bin _ kx x l r)  = balance kx x l (deleteMax r)
deleteMax Tip               = Tip

union :: Ord k => Map k a -> Map k a -> Map k a
union Tip t2 = t2
union t1 Tip = t1
union t1 t2 = hedgeUnionL (const LT) (const GT) t1 t2

-- left-biased hedge union
hedgeUnionL :: Ord a
            => (a -> Ordering) -> (a -> Ordering) -> Map a b -> Map a b
            -> Map a b
hedgeUnionL _     _     t1 Tip
  = t1
hedgeUnionL cmplo cmphi Tip (Bin _ kx x l r)
  = join kx x (filterGt cmplo l) (filterLt cmphi r)
hedgeUnionL cmplo cmphi (Bin _ kx x l r) t2
  = join kx x (hedgeUnionL cmplo cmpkx l (trim cmplo cmpkx t2)) 
              (hedgeUnionL cmpkx cmphi r (trim cmpkx cmphi t2))
  where
    cmpkx k  = compare kx k


{--------------------------------------------------------------------
  [trim lo hi t] trims away all subtrees that surely contain no
  values between the range [lo] to [hi]. The returned tree is either
  empty or the key of the root is between @lo@ and @hi@.
--------------------------------------------------------------------}
trim :: (k -> Ordering) -> (k -> Ordering) -> Map k a -> Map k a
trim _     _     Tip = Tip
trim cmplo cmphi t@(Bin _ kx _ l r)
  = case cmplo kx of
      LT -> case cmphi kx of
              GT -> t
              _  -> trim cmplo cmphi l
      _  -> trim cmplo cmphi r

{--------------------------------------------------------------------
  Join 
--------------------------------------------------------------------}
join :: Ord k => k -> a -> Map k a -> Map k a -> Map k a
join kx x Tip r  = insertMin kx x r
join kx x l Tip  = insertMax kx x l
join kx x (Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz)
  | delta*sizeL <= sizeR  = balance kz z (join kx x (Bin sizeL ky y ly ry) lz) rz
  | delta*sizeR <= sizeL  = balance ky y ly (join kx x ry (Bin sizeR kz z lz rz))
  | otherwise             = bin kx x (Bin sizeL ky y ly ry) (Bin sizeR kz z lz rz)

-- insertMin and insertMax don't perform potentially expensive comparisons.
insertMax,insertMin :: k -> a -> Map k a -> Map k a 
insertMax kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balance ky y l (insertMax kx x r)
             
insertMin kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balance ky y (insertMin kx x l) r

{--------------------------------------------------------------------
  [filterGt k t] filter all keys >[k] from tree [t]
  [filterLt k t] filter all keys <[k] from tree [t]
--------------------------------------------------------------------}
filterGt :: Ord k => (k -> Ordering) -> Map k a -> Map k a
filterGt _   Tip = Tip
filterGt cmp (Bin _ kx x l r)
  = case cmp kx of
      LT -> join kx x (filterGt cmp l) r
      GT -> filterGt cmp r
      EQ -> r
      
filterLt :: Ord k => (k -> Ordering) -> Map k a -> Map k a
filterLt _   Tip = Tip
filterLt cmp (Bin _ kx x l r)
  = case cmp kx of
      LT -> filterLt cmp l
      GT -> join kx x l (filterLt cmp r)
      EQ -> l

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


chkDel x Tip                = assert True  
chkDel x (Bin sz k v lt rt) = assert (not (x == k)) && chkDel x lt && chkDel x rt

chkMin x Tip                = assert True  
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
bst2 = mkBst $ zip [1..] [1..]

mkBst = foldl (\t (k, v) -> insert k v t) Tip

prop        = chk bst1
prop1       = chk $ mkBst $ zip [1..] [1..]

propDeleteMin = chk $ deleteMin bst
propDeleteMax = chk $ deleteMax bst

propAlter  = chk $ alter f x bst2
   where x = choose 0
         f _ = Nothing 
propDelete  = chk $ delete x bst
   where x = choose 0

propJoin  = chk $ join kx k l r
   where Bin _ kx k l r = bst2




























