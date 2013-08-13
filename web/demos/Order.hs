{-# LANGUAGE NoMonomorphismRestriction #-}

{-@ LIQUID "--notermination"           @-}

module PuttingThingsInOrder where

import Prelude hiding (break)

-- Haskell Type Definitions
plusOnes     :: [(Int, Int)]
insertSort   :: (Ord a) => [a] -> [a]
mergeSort    :: (Ord a) => [a] -> [a]
quickSort    :: (Ord a) => [a] -> [a]
digits       :: Assoc String
sparseVec    :: Assoc Double
digsVec      :: Vec Int
whatGosUp    :: [Integer]
mustGoDown   :: [Integer]
noDuplicates :: [Integer]


-- Polymorphic Association Lists

data AssocP k v = KVP [(k, v)]


{-@ digitsP :: AssocP {v:Int | (Btwn 0 v 9)} String @-}
digitsP :: AssocP Int String
digitsP = KVP [ (1, "one")
              , (2, "two")
              , (3, "three") ]

{-@ sparseVecP :: AssocP {v:Int | (Btwn 0 v 1000)} Double @-}
sparseVecP :: AssocP Int Double
sparseVecP = KVP [ (12 ,  34.1 )
                 , (92 , 902.83)
                 , (451,   2.95)
                 , (877,   3.1 )]


{-@ predicate Btwn Lo V Hi = (Lo <= V && V <= Hi) @-}

-- Monomorphic Association Lists
-- -----------------------------

{-@ data Assoc v <p :: Int -> Prop> = KV (z :: [(Int<p>, v)]) @-}
data Assoc v = KV [(Int, v)]



{-@ digits :: Assoc (String) <{\v -> (Btwn 0 v 9)}> @-}
digits    = KV [ (1, "one")
               , (2, "two")
               , (3, "three") ]


{-@ sparseVec :: Assoc Double <{\v -> (Btwn 0 v 1000)}> @-}
sparseVec = KV [ (12 ,  34.1 )
               , (92 , 902.83)
               , (451,   2.95)
               , (877,   3.1 )]



-- Dependent Tuples
-- ----------------

-- `break` from the Prelude.

break                   :: (a -> Bool) -> [a] -> ([a], [a])
break _ xs@[]           =  (xs, xs)
break p xs@(x:xs')
           | p x        =  ([], xs)
           | otherwise  =  let (ys, zs) = break p xs'
                           in (x:ys,zs)

-- Dependent Tuples via Abstract Refinements
-- 
-- data (a,b)<p :: a -> b -> Prop> = (x:a, b<p x>)

-- Instantiate the `p` in *different* ways.

{-@ plusOnes :: [(Int, Int)<{\x1 x2 -> x2 = x1 + 1}>] @-}
plusOnes = [(0,1), (5,6), (999,1000)]

{-@ break :: (a -> Bool) -> x:[a]
          -> ([a], [a])<{\y z -> (Break x y z)}> @-}

{-@ predicate Break X Y Z   = (len X) = (len Y) + (len Z) @-}

---------------------------------------------------------------
-- Abstractly Refined Lists
---------------------------------------------------------------

-- data [a] <p :: a -> a -> Prop> 
--   = []  
--   | (:) (hd :: a) (tl :: [a<p h>]<p>) -> [a]<p>

-- * The type is parameterized with a refinement `p :: a -> a -> Prop`
--   Think of `p` as a *binary relation* over the `a` values comprising
--   the list.

-- * The empty list `[]` is a `[a]<p>`. Clearly, the empty list has no
--   elements whatsoever and so every pair is trivially, or rather,
--   vacuously related by `p`.

-- * The cons constructor `(:)` takes a head `hd` of type `a` and a tail
--   `tl` of `a<p h>` values, each of which is *related to* `h` **and** which
--   (recursively) are pairwise related `[...]<p>` and returns a list where
--   *all* elements are pairwise related `[a]<p>`.


---------------------------------------------------------------
-- Using Abstractly Refined Lists
---------------------------------------------------------------

-- For starters, we can define a few helpful type aliases.

{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}
{-@ type DecrList a = [a]<{\xi xj -> xi >= xj}> @-}
{-@ type UniqList a = [a]<{\xi xj -> xi /= xj}> @-}


{-@ whatGosUp :: IncrList Integer @-}
whatGosUp = [1,2,3]


{-@ mustGoDown :: DecrList Integer @-}
mustGoDown = [3,2,1]


{-@ noDuplicates :: UniqList Integer @-}
noDuplicates = [1,3,2]


---------------------------------------------------------------
-- Insertion Sort ---------------------------------------------
---------------------------------------------------------------

{-@ insertSort    :: (Ord a) => xs:[a] -> (IncrList a) @-}
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)

{-@ insert :: (Ord a) => a -> IncrList a -> IncrList a @-}
insert y []     = [y]
insert y (x:xs)
  | y <= x      = y : x : xs
  | otherwise   = x : insert y xs


-- If you prefer the more Haskelly way of writing insertion sort,
-- i.e. with a `foldr`, that works too. Can you figure out why?

{-@ insertSort' :: (Ord a) => [a] -> IncrList a @-}
insertSort' xs  = foldr insert [] xs


---------------------------------------------------------------
-- Merge Sort -------------------------------------------------
---------------------------------------------------------------

split          :: [a] -> ([a], [a])
split (x:y:zs) = (x:xs, y:ys)
  where
    (xs, ys)   = split zs
split xs       = (xs, [])


{-@ merge :: (Ord a) => IncrList a -> IncrList a -> IncrList a @-}
merge xs []         = xs
merge [] ys         = ys
merge (x:xs) (y:ys)
  | x <= y          = x : merge xs (y:ys)
  | otherwise       = y : merge (x:xs) ys

{-@ mergeSort :: (Ord a) => [a] -> IncrList a @-}
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
    (ys, zs)  = split xs

---------------------------------------------------------------
-- Quick Sort -------------------------------------------------
---------------------------------------------------------------


{-@ quickSort    :: (Ord a) => [a] -> IncrList a @-}
quickSort []     = []
quickSort (x:xs) = pivApp x lts gts
  where
    lts          = quickSort [y | y <- xs, y < x ]
    gts          = quickSort [z | z <- xs, z >= x]

pivApp piv []     ys  = piv : ys
pivApp piv (x:xs) ys  = x   : pivApp piv xs ys


-- Really Sorting Lists
-- --------------------

-- The convenient thing about our encoding is that the
-- underlying datatype is plain Haskell lists.
-- By decoupling (or rather, parameterizing)
-- the relation or property or invariant from the actual
-- data structure we can plug in different invariants,
-- sometimes in the *same* program.

-- To see why this is useful, lets look at a *real-world*
-- sorting algorithm: the one used inside GHC's
-- `Data.List` [module][ghc-list].

{-@ sort :: (Ord a) => [a] -> IncrList a  @-}
sort = mergeAll . sequences
  where
    sequences (a:b:xs)
      | a `compare` b == GT = descending b [a]  xs
      | otherwise           = ascending  b (a:) xs
    sequences [x] = [[x]]
    sequences []  = [[]]

    descending a as (b:bs)
      | a `compare` b == GT = descending b (a:as) bs
    descending a as bs      = (a:as): sequences bs

    ascending a as (b:bs)
      | a `compare` b /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs       = as [a]: sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = merge a b: mergePairs xs
    mergePairs [x]      = [x]
    mergePairs []       = []


---------------------------------------------------------------
-- User-defined Lists
---------------------------------------------------------------

-- The earlier definition is baked into LiquidHaskell's prelude,
-- since its for GHC Lists.
-- For completeness, lets illustrate the method on a new list type.

data Vec a = Null | Cons a (Vec a)

{-@ data Vec a <p :: a -> a -> Prop> 
      = Null
      | Cons (h :: a) (t :: Vec <p> (a<p h>))
  @-}

{-@ type IncrVec a = Vec <{\xi xj -> xi <= xj}> a @-}

{-@ digsVec :: IncrVec Int @-}
digsVec     = Cons 0 (Cons 1 (Cons 2 Null))

