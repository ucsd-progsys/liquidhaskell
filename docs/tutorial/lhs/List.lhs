\begin{code}
module List where
\end{code}

Recursive Invariants
====================

Remember the definition of List
\begin{code}
infixr `C`
data L a = N | C a (L a)
\end{code}

We can parameterize the definition with an abstract refinement `p`
that relates the head of the list with all the elements of the tail:

\begin{code}
{-@ data L a <p :: a -> a -> Prop>
      = N 
      | C (h :: a) (tl :: (L <p> a<p h>))
  @-}
\end{code}

\begin{code} Consider a list with three elements:
h1 `C` h2 `C` h3 `C` N :: L <p> a 
\end{code}

\begin{code} If we unfold the list once we get:
h1              :: a
h2 `C` h3 `C` N :: L <p> a<p h1> 
\end{code}

\begin{code} With a second unfold we get:
h1       :: a
h2       :: a<p h1>  
h3 `C` N :: L <p> a<p h1 && p h2> 
\end{code}

\begin{code} Finally, with one more unfold we get:
h1 :: a
h2 :: a<p h1>  
h3 :: a<p h1 && p h2>  
N  :: L <p> a<p h1 && p h2 && p h3> 
\end{code}
So `p` hold between *every pair* of elements in the list. 


Consinder instantiating the abstract refinement with a concrete one
stating that the value is less than the head, expressing increasing lists:

\begin{code}
{-@ type SL a = L <{\hd v -> v >= hd}> a @-}
\end{code}

We can verify that a random increasing list actually enjoys this type.
\begin{code}
{-@ slist :: SL Int @-}
slist :: L Int
slist = 1 `C` 6 `C` 12 `C` N
\end{code}


InsertSort
----------
More interestingly, we can verify that various *recursive* sorting algorithms return sorted lists.
\begin{code}
{-@ insert' :: (Ord a) => a -> SL a -> SL a @-}
insert'     :: (Ord a) => a -> L a -> L a
insert' y N                      = y `C` N                           
insert' y (x `C` xs) | y <= x    = y `C` x `C` xs
                     | otherwise = x `C` insert' y xs


{-@ insertSort' :: (Ord a) => [a] -> SL a @-}
insertSort'     :: (Ord a) => [a] -> L a
insertSort'     = foldr insert' N
\end{code}


On Haskell Lists
----------------

[Demo](http://goto.ucsd.edu/~rjhala/liquid/haskell/demo/#?demo=ListSort.hs)

\begin{code}We have hacked the Haskell List definition to abstract over a refinement:
data [a] <p :: a -> a -> Prop>
  = [] 
  | (:) (h :: a) (tl :: ([a<p h>]<p>))
  @-}
\end{code}

So, we can define `insertSort` on *real* lists

\begin{code}
{-@ type OList a = [a]<{\fld v -> (v >= fld)}> @-}
\end{code}

InsertSort
----------
\begin{code}
{-@ insertSort :: (Ord a) => xs:[a] -> OList a @-}
insertSort xs  = foldr insert [] xs

insert y []                   = [y]
insert y (x : xs) | y <= x    = y : x : xs 
                  | otherwise = x : insert y xs
\end{code}

MergeSort
---------
\begin{code}
{-@ mergeSort :: (Ord a) => [a] -> OList a @-}
mergeSort     :: Ord a => [a] -> [a]
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort xs1) (mergeSort xs2) where (xs1, xs2) = split xs

split :: [a]    -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs         = (xs, [])

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) | x <= y    = x:(merge xs (y:ys))
                    | otherwise = y:(merge (x:xs) ys)
\end{code}

QuickSort
---------
\begin{code}
{-@ quickSort    :: (Ord a) => [a] -> OList a @-}
quickSort []     = []
quickSort (x:xs) = append x lts gts 
  where lts = quickSort [y | y <- xs, y < x]
        gts = quickSort [z | z <- xs, z >= x]

append k []     ys  = k : ys
append k (x:xs) ys  = x : append k xs ys
\end{code}


Maps
====
[Demo](http://goto.ucsd.edu/~rjhala/liquid/haskell/demo/#?demo=Map.hs)

As another application of recursive refinements, 
consinder a Map from keys of type `k` to values of type `a` 
implemented as a binary tree:

\begin{code}
data Map k a = Tip
             | Bin Size k a (Map k a) (Map k a)

type Size    = Int
\end{code}

We abstract from the structure two refinements `l` and `r`
to describe the values of the left and right subtree with respect to the
current key:

\begin{code}
{-@
  data Map k a <l :: root:k -> k -> Prop, r :: root:k -> k -> Prop>
      = Tip
      | Bin (sz    :: Size)
            (key   :: k)
            (value :: a)
            (left  :: Map <l, r> (k <l key>) a)
            (right :: Map <l, r> (k <r key>) a)
  @-}
\end{code}

Thus, if we instantiate the refinements with the following predicates

\begin{code}
{-@ type BST k a     = Map <{\r v -> v < r }, {\r v -> v > r }> k a @-}
{-@ type MinHeap k a = Map <{\r v -> r <= v}, {\r v -> r <= v}> k a @-}
{-@ type MaxHeap k a = Map <{\r v -> r >= v}, {\r v -> r >= v}> k a @-}
\end{code}

then `BST k v`, `MinHeap k v` and `MaxHeap k v` denote exactly binary-search-ordered, min-heap-ordered, and max-heap-ordered trees (with keys and values of types `k` and `v`).

We can use the above types to automatically verify that the following functions preserve BST.

Empty
-----
\begin{code}
{-@ empty :: BST k a @-}
empty     :: Map k a
empty     = Tip
\end{code}

Insert
------
\begin{code}
{-@ insertBST :: Ord k => k:k -> a:a -> t:BST k a -> BST k a @-}
insertBST     :: Ord k => k -> a -> Map k a -> Map k a
insertBST kx x t
  = case t of
     Tip -> singleton kx x
     Bin sz ky y l r
         -> case compare kx ky of
              LT -> balance ky y (insertBST kx x l) r
              GT -> balance ky y l (insertBST kx x r)
              EQ -> Bin sz kx x l r
\end{code}

Delete 
------

\begin{code}
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
\end{code}

Below are the functions used by `insert` and `delete`:
\begin{code}
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


balance :: k -> a -> Map k a -> Map k a -> Map k a
balance k x l r = undefined

bin :: k -> a -> Map k a -> Map k a -> Map k a
bin k x l r
  = Bin (size l + size r + 1) k x l r

size :: Map k a -> Int
size t
  = case t of
      Tip            -> 0
      Bin sz _ _ _ _ -> sz
\end{code}
