module Map where

-- | In this example, we show how we can use multi-parameter abstract refinements
-- to encode ordering invarants on binary search trees.

-- The following code ins from Data.Map


{-@
  data Map k a <l :: k -> k -> Prop, r :: k -> k -> Prop>
      = Tip
      | Bin (sz    :: Size)
            (key   :: k)
            (value :: a)
            (left  :: Map <l, r> (k <l key>) a)
            (right :: Map <l, r> (k <r key>) a)
  @-}

data Map k a = Tip
             | Bin Size k a (Map k a) (Map k a)

type Size    = Int


-- The abstract refinements `l` and `r` relate each `key` of the tree with `all` the keys in the `left` and `right` subtrees of `key`, as those keys are respectively of type `k <l key>` and `k <r key>`.

-- Thus, if we instantiate the refinements with the following predicates


{-@ type BST k a     = Map <{\r v -> v < r }, {\r v -> v > r }> k a @-}
{-@ type MinHeap k a = Map <{\r v -> r <= v}, {\r v -> r <= v}> k a @-}
{-@ type MaxHeap k a = Map <{\r v -> r >= v}, {\r v -> r >= v}> k a @-}


-- then `BST k v`, `MinHeap k v` and `MaxHeap k v` denote exactly binary-search-ordered, min-heap-ordered, and max-heap-ordered trees (with keys and values of types `k` and `v`).

-- We can use the above types to automatically verify that the following functions preserve BST.

{-@ empty :: BST k a @-}
empty     :: Map k a
empty     = Tip

{-@ insert :: Ord k => k:k -> a:a -> t:BST k a -> BST k a @-}
insert :: Ord k => k -> a -> Map k a -> Map k a
insert kx x t
  = case t of
     Tip -> singleton kx x
     Bin sz ky y l r
         -> case compare kx ky of
              LT -> balance ky y (insert kx x l) r
              GT -> balance ky y l (insert kx x r)
              EQ -> Bin sz kx x l r

{-@ delete :: (Ord k) => k:k -> t:BST k a -> BST k a @-}
delete :: Ord k => k -> Map k a -> Map k a
delete k t
  = case t of
      Tip -> Tip
      Bin _ kx x l r
          -> case compare k kx of
               LT -> balance kx x (delete k l) r
               GT -> balance kx x l (delete k r)
               EQ -> glue kx l r

-- Below are the functions used by `insert` and `delete`:

singleton :: k -> a -> Map k a
singleton k x
  = Bin 1 k x Tip Tip


glue :: k -> Map k a -> Map k a -> Map k a
glue k Tip r = r
glue k l Tip = l
glue k l r
  | size l > size r = let (km1, vm, lm) = deleteFindMax l in balance km1 vm lm r
  | otherwise       = let (km2, vm, rm) = deleteFindMin r in balance km2 vm l rm

deleteFindMax t
  = case t of
      Bin _ k x l Tip -> (k, x, l)
      Bin _ k x l r -> let (km3, vm, rm) = deleteFindMax r in
                       (km3, vm, (balance k x l rm))
      Tip           -> (error ms, error ms, Tip)
  where ms = "Map.deleteFindMax : can not return the maximal element of an empty Map"


deleteFindMin t
  = case t of
      Bin _ k x Tip r -> (k, x, r)
      Bin _ k x l r -> let (km4, vm, lm) = deleteFindMin l in
                       (km4, vm, (balance k x lm r))
      Tip             -> (error ms, error ms, Tip)
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
rotateR _ _ Tip _ = error "rotateR Tip"

-- basic rotations
singleL, singleR :: a -> b -> Map a b -> Map a b -> Map a b
singleL k1 x1 t1 (Bin _ k2 x2 t2 t3) = bin k2 x2 (bin k1 x1 t1 t2) t3
singleL _  _  _ Tip = error "sinlgeL Tip"
singleR k1 x1 (Bin _ k2 x2 t1 t2) t3 = Bin 0 k2 x2 t1 (Bin 0 k1 x1 t2 t3)
singleR _  _  Tip _ = error "sinlgeR Tip"

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

