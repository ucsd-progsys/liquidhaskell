% Recursive Invariants

Recursive Invariants
--------------------

\begin{code}
module List where

{-@ LIQUID "--no-termination" @-}
\end{code}


Recursive Invariants
--------------------

Recall the definition of lists <br>

\begin{code}
infixr `C`
data L a = N | C a (L a)
\end{code}

Lets parameterize the definition with an abstract refinement `p` <br>

\begin{code}
{-@ data L a <p :: a -> a -> Prop>
      = N 
      | C (h :: a) (tl :: (L <p> a<p h>))
  @-}
\end{code}

- `p` is a binary relation between two `a` values

- definition relates *head* with all the *tail* elements 

**Recursive** : So `p` holds between **every pair** of list elements!

Recursive Invariants: Example
-----------------------------

Consider a list with three elements <br>

\begin{code} _ 
h1 `C` h2 `C` h3 `C` N :: L <p> a 
\end{code}

Recursive Invariants: Example
-----------------------------

If we unfold the list **once** we get <br>

\begin{code} _
h1              :: a
h2 `C` h3 `C` N :: L <p> a<p h1> 
\end{code}

Recursive Invariants: Example
-----------------------------

If we unfold the list a **second** time we get <br>

\begin{code} _ 
h1       :: a
h2       :: a<p h1>  
h3 `C` N :: L <p> a<p h1 && p h2> 
\end{code}

Recursive Invariants: Example
-----------------------------

Finally, with a **third** unfold we get <br>

\begin{code} _ 
h1 :: a
h2 :: a<p h1>  
h3 :: a<p h1 && p h2>  
N  :: L <p> a<p h1 && p h2 && p h3> 
\end{code}

<br>

Note how `p` holds between **every pair** of elements in the list. 

Using Recursive Invariants
--------------------------

That was a rather *abstract*.

How would we **use** the fact that `p` holds between **every pair** ?


Using Recursive Invariants
--------------------------

That was a rather *abstract*.

How would we **use** the fact that `p` holds between **every pair** ?

<br>

Lets *instantiate* `p` with a concrete refinement 

<br>

\begin{code}
{-@ type SL a = L <{\hd v -> hd <= v}> a @-}
\end{code}

- The refinement says `hd` is less than the arbitrary tail element `v`.

- Thus `SL` denotes lists sorted in **increasing order**!

Using Recursive Invariants
--------------------------

LiquidHaskell verifies that the following list is indeed increasing...

<br>

\begin{code}
{-@ slist :: SL Int @-}
slist :: L Int
slist = 1 `C` 6 `C` 12 `C` N
\end{code}

<br> ... and complains that the following is not: <br>


\begin{code}
{-@ slist' :: SL Int @-}
slist' :: L Int
slist' = 6 `C` 1 `C` 12 `C` N
\end{code}


InsertSort
----------

More interestingly, we can verify that various sorting algorithms return sorted lists.

<br>

\begin{code}
{-@ insertSort' :: (Ord a) => [a] -> SL a @-}
insertSort'     :: (Ord a) => [a] -> L a 
insertSort'     = foldr insert' N
\end{code}

<br> The hard work is done by `insert` defined as <br>

\begin{code}
insert' y N                      = y `C` N                           
insert' y (x `C` xs) | y <= x    = y `C` x `C` xs
                     | otherwise = x `C` insert' y xs
\end{code}

<br>

**Hover** the mouse over `insert'` to see what type was inferred for it.

Analyzing Plain Lists
---------------------

<a href="http://goto.ucsd.edu:8090/index.html#?demo=Order.hs" target= "_blank">Demo:</a> 


We can easily modify GHC's List definition to abstract over a refinement:

<br>

\begin{code} _
data [a] <p :: a -> a -> Prop>
  = [] 
  | (:) (h :: a) (tl :: ([a<p h>]<p>))
\end{code}

<br>

So, we can define and use **ordered** versions of GHC Lists

<br>

\begin{code}
{-@ type OList a = [a]<{\hd v -> (hd <= v)}> @-}
\end{code}

Insertion Sort
--------------

Now we can verify the usual sorting algorithms: 

<br>

\begin{code}
{-@ insertSort :: (Ord a) => xs:[a] -> OList a @-}
insertSort xs  = foldr insert [] xs
\end{code}

<br> 

where the helper does the work

<br>

\begin{code}
insert y []                   = [y]
insert y (x : xs) | y <= x    = y : x : xs 
                  | otherwise = x : insert y xs
\end{code}

Merge Sort
----------

Now we can verify the usual sorting algorithms: 


\begin{code}
{-@ mergeSort :: (Ord a) => [a] -> OList a @-}
mergeSort     :: Ord a => [a] -> [a]
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort xs1) (mergeSort xs2) 
  where 
   (xs1, xs2) = split xs

split :: [a]    -> ([a], [a])
split (x:(y:zs)) = (x:xs, y:ys) where (xs, ys) = split zs
split xs         = (xs, [])

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) | x <= y    = x:(merge xs (y:ys))
                    | otherwise = y:(merge (x:xs) ys)
\end{code}

<br> A significant amount of inference happens above. See the types.

QuickSort
---------

Now we can verify the usual sorting algorithms: <br>

\begin{code}
{-@ quickSort    :: (Ord a) => [a] -> OList a @-}
quickSort []     = []
quickSort (x:xs) = append x lts gts 
  where 
    lts          = quickSort [y | y <- xs, y < x]
    gts          = quickSort [z | z <- xs, z >= x]
\end{code}

<br> We require a special `append` parameterized by the **pivot** <br>

\begin{code}
append k []     ys  = k : ys
append k (x:xs) ys  = x : append k xs ys
\end{code}

Look at the inferred type to understand why!


Other Instantiations: Decreasing Lists
--------------------------------------

We may *instantiate* `p` with many different concrete relations

<br> **Decreasing Lists** <br>

\begin{code}
{-@ type DecrList a = [a]<{\hd v -> (hd >= v)}> @-}
\end{code}

<br> After which we can check that <br>

\begin{code}
{-@ decList :: DecrList Int @-}
decList :: [Int]
decList = [3, 2, 1, 0]
\end{code}

Multiple Instantiations: Distinct Lists 
---------------------------------------

We may *instantiate* `p` with many different concrete relations

<br> **Distinct Lists**: Lists not containing any duplicate values <br>

\begin{code}
{-@ type DiffList a = [a]<{\hd v -> (hd /= v)}> @-}
\end{code}

<br> After which we can check that <br>

\begin{code}
{-@ diffList :: DiffList Int @-}
diffList :: [Int]
diffList = [2, 3, 1, 0]
\end{code}

Binary Trees 
------------


- Consider a `Map` from keys of type `k` to values of type `a` 

- Implemented as a binary tree:

\begin{code}
data Map k a = Tip
             | Bin Size k a (Map k a) (Map k a)

type Size    = Int
\end{code}

Binary Trees 
------------

We abstract from the structure two refinements `l` and `r` 

- `l` relates root `key` with **left**-subtree keys

- `r` relates root `key` with **right**-subtree keys

\begin{code}
{-@
  data Map k a <l :: k -> k -> Prop, r :: k -> k -> Prop>
      = Tip
      | Bin (sz    :: Size)
            (key   :: k)
            (value :: a)
            (left  :: Map <l, r> (k <l key>) a)
            (right :: Map <l, r> (k <r key>) a)
  @-}
\end{code}


Ordered Trees
-------------

Thus, if we instantiate the refinements thus: 

<br>

\begin{code}
{-@ type BST k a     = Map <{\r v -> v < r }, {\r v -> v > r }> k a @-}
{-@ type MinHeap k a = Map <{\r v -> r <= v}, {\r v -> r <= v}> k a @-}
{-@ type MaxHeap k a = Map <{\r v -> r >= v}, {\r v -> r >= v}> k a @-}
\end{code}

- `BST k v` denotes **binary-search** ordered trees

- `MinHeap k v` denotes **min-heap** ordered trees

- `MaxHeap k v` denotes **max-heap** ordered trees.

Binary Search Ordering
----------------------

We can use the `BST` type to automatically verify that tricky functions
ensure and preserve binary-search ordering.

<a href="http://goto.ucsd.edu:8090/index.html#?demo=Map.hs" target= "_blank">Demo:</a> 

\begin{code}So, we can have
empty :: BST k a

insert :: Ord k => k:k -> a:a -> t:BST k a -> BST k a

delete :: (Ord k) => k:k -> t:BST k a -> BST k a
\end{code}

Binary Search Ordering: Empty
-----------------------------

\begin{code}
{-@ empty :: BST k a @-}
empty     :: Map k a
empty     = Tip
\end{code}

Binary Search Ordering: Insert
------------------------------

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

Binary Search Ordering: Delete 
------------------------------

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


Helper Functions: Constructors
------------------------------

Below are the helper functions used by `insert` and `delete`:

\begin{code}
singleton :: k -> a -> Map k a
singleton k x
  = Bin 1 k x Tip Tip

bin :: k -> a -> Map k a -> Map k a -> Map k a
bin k x l r
  = Bin (size l + size r + 1) k x l r

size :: Map k a -> Int
size t
  = case t of
      Tip            -> 0
      Bin sz _ _ _ _ -> sz
\end{code}

Helper Functions: Extractors 
----------------------------

\begin{code}
deleteFindMax t
  = case t of
      Bin _ k x l Tip -> (k, x, l)
      Bin _ k x l r -> let (km3, vm, rm) = deleteFindMax r in
                       (km3, vm, (balance k x l rm))
      Tip           -> (error ms, error ms, Tip)
  where 
    ms = "Map.deleteFindMax : empty Map"

deleteFindMin t
  = case t of
      Bin _ k x Tip r -> (k, x, r)
      Bin _ k x l r -> let (km4, vm, lm) = deleteFindMin l in
                       (km4, vm, (balance k x lm r))
      Tip             -> (error ms, error ms, Tip)
  where 
    ms = "Map.deleteFindMin : empty Map"
\end{code}

Helper Functions: Connectors 
----------------------------

Below are the helper functions used by `insert` and `delete`:

\begin{code}
glue :: k -> Map k a -> Map k a -> Map k a
glue k Tip r = r
glue k l Tip = l
glue k l r
  | size l > size r = let (km1, vm, lm) = deleteFindMax l 
                      in balance km1 vm lm r

  | otherwise       = let (km2, vm, rm) = deleteFindMin r 
                      in balance km2 vm l rm

{-@ balance :: key:k 
            -> a 
            -> (BST {v:k | v < key} a) 
            -> (BST {v:k| key < v} a) -> (BST k a) @-}
balance :: k -> a -> Map k a -> Map k a -> Map k a
balance k x l r = undefined
\end{code}



