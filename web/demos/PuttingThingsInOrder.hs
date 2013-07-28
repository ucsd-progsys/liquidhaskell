{--! run liquid with no-termination -}

module PuttingThingsInOrder where

import Prelude hiding (break)

-- Haskell Type Definitions
plusOnes                         :: [(Int, Int)]
insertSort, mergeSort, quickSort :: (Ord a) => [a] -> [a]


-- Polymorphic Association Lists

data AssocP k v = KVP [(k, v)]


-- Now, in a program, you might have multiple association
-- lists, whose keys satisfy different properties.
-- For example, we might have a table for mapping digits
-- to the corresponding English string


digitsP :: AssocP Int String
digitsP = KVP [ (1, "one")
              , (2, "two")
              , (3, "three") ]


-- We could have a separate table for *sparsely* storing
-- the contents of an array of size `1000`.

sparseVecP :: AssocP Int Double
sparseVecP = KVP [ (12 ,  34.1 )
                 , (92 , 902.83)
                 , (451,   2.95)
                 , (877,   3.1 )]

-- The **keys** used in the two tables have rather
-- different properties, which we may want to track
-- at compile time.

-- 1. In `digitsP` the keys are between `0` and `9`
-- 2. In `sparseVecP` the keys are between `0` and `999`.

-- We can express the above properties by instantiating
-- the type of `k` with refined versions

{-@ digitsP :: AssocP {v:Int | (Btwn 0 v 9)} String @-}


{-@ sparseVecP :: AssocP {v:Int | (Btwn 0 v 1000)} Double @-}


{-@ predicate Btwn Lo V Hi = (Lo <= V && V <= Hi) @-}


-- Monomorphic Association Lists
-- -----------------------------

data Assoc v = KV [(Int, v)]

-- Now, we have our two tables

digits    :: Assoc String
digits    = KV [ (1, "one")
               , (2, "two")
               , (3, "three") ]

sparseVec :: Assoc Double
sparseVec = KV [ (12 ,  34.1 )
               , (92 , 902.83)
               , (451,   2.95)
               , (877,   3.1 )]


-- Abstractly Refined Data
-- -----------------------

{-@ data Assoc v <p :: Int -> Prop>
      = KV (z :: [(Int<p>, v)]) @-}

{-@ digits :: Assoc (String) <{\v -> (Btwn 0 v 9)}> @-}

{-@ sparseVec :: Assoc Double <{\v -> (Btwn 0 v 1000)}> @-}


-- Dependent Tuples
-- ----------------

-- `break` from the Prelude.

break                   :: (a -> Bool) -> [a] -> ([a], [a])
break _ xs@[]           =  (xs, xs)
break p xs@(x:xs')
           | p x        =  ([], xs)
           | otherwise  =  let (ys, zs) = break p xs'
                           in (x:ys,zs)

-- \begin{code} Instead, lets use abstract refinements to give us **dependent tuples**
-- data (a,b)<p :: a -> b -> Prop> = (x:a, b<p x>)
-- \end{code}

-- The abstract refinement takes two parameters,
-- an `a` and a `b`. In the body of the tuple, the
-- first element is named `x` and we specify that
-- the second element satisfies the refinement `p x`,
-- i.e. a partial application of `p` with the first element.
-- In other words, the second element is a value of type
-- `{v:b | (p x v)}`.

-- As before, we can instantiate the `p` in *different* ways.

{-@ plusOnes :: [(Int, Int)<{\x v -> v = x + 1}>] @-}
plusOnes = [(0,1), (5,6), (999,1000)]


{-@ break :: (a -> Bool) -> x:[a]
          -> ([a], [a])<{\y z -> (Break x y z)}> @-}

{-@ predicate Break X Y Z   = (len X) = (len Y) + (len Z) @-}


-- Abstractly Refined Lists
-- ------------------------

-- data [a] <p :: a -> a -> Prop> where
--   | []  :: [a] <p>
--   | (:) :: h:a -> [a<p h>]<p> -> [a]<p>

-- * The type is parameterized with a refinement `p :: a -> a -> Prop`
--   Think of `p` as a *binary relation* over the `a` values comprising
--   the list.

-- * The empty list `[]` is a `[]<p>`. Clearly, the empty list has no
--   elements whatsoever and so every pair is trivially, or rather,
--   vacuously related by `p`.

-- * The cons constructor `(:)` takes a head `h` of type `a` and a tail
--   of `a<p h>` values, each of which is *related to* `h` **and** which
--   (recursively) are pairwise related `[...]<p>` and returns a list where
--   *all* elements are pairwise related `[a]<p>`.

-- Using Abstractly Refined Lists
-- ------------------------------

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


-- Sorting Lists
-- -------------

-- **Insertion Sort**

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


-- **Merge Sort**


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


-- **Quick Sort**


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

    mergePairs (a:b:xs) = merge1 a b: mergePairs xs
    mergePairs [x]      = [x]
    mergePairs []       = []


merge1 (a:as') (b:bs')
  | a `compare` b == GT = b:merge1 (a:as')  bs'
  | otherwise           = a:merge1 as' (b:bs')
merge1 [] bs            = bs
merge1 as []            = as


