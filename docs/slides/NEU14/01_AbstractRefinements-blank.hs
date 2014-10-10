{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}

module AbstractRefinements (
    listMax
  , insertSort
  , insertSort'
  ) where


import Data.Set hiding (insert, foldr,size) 
import Prelude hiding (map, foldr)



-----------------------------------------------------------------------
-- | 0. Abstract Refinements 
-----------------------------------------------------------------------


-- Warmup: How shall we type listMax?

listMax     :: [Int] -> Int
listMax xs  = foldr1 max xs 






-- Lets define a few different subsets of Int

-- Even
-- Odd
-- RGB


-- compute the largest of some lists

{- xE :: Even -}
xE = listMax [0, 200, 4000, 60] 



{- xO :: Odd -}
xO = listMax [1, 21, 4001, 961] 



{- xR :: RGB -}
xR = listMax [1, 21, 41, 61] 


-- Why do we get the errors? How do we fix it?









-----------------------------------------------------------------------
-- | 1. Abstract Refinement from List's Type 
-----------------------------------------------------------------------

-- data List a <p> 










-----------------------------------------------------------------------
-- | 2. Instantiating Abstract Refinements 
-----------------------------------------------------------------------


{- type IncrList a -} 
{- type DecrList a -} 
{- type DiffList a -} 

ups   = undefined

downs = undefined

diffs = undefined


-----------------------------------------------------------------------
-- | 3. Insertion Sort: Revisited
-----------------------------------------------------------------------

{- insert         :: _ -> xs:_ -> {v:_ | size v = 1 + size xs} -}
insert x N         = x `C` N
insert x (C y ys)
  | x <= y         = x `C` y `C` ys
  | otherwise      = y `C` insert x ys 



{- insertSort      :: xs:List a -> {v:IncrList a | EqSize v xs} -}
insertSort N        = N
insertSort (C x xs) = insert x (insertSort xs)











-----------------------------------------------------------------------
-- | 3. Insertion Sort: using a `foldr` 
-----------------------------------------------------------------------


insertSort' = undefined














-----------------------------------------------------------------------
-- | 4. But, there are limits...
-----------------------------------------------------------------------

-- how big is the list returned by insertSort' ?


-- Hmm. Thats a bummer... How do we type `foldr` to verify the above?











-----------------------------------------------------------------------
-- | 5. Induction, as an Abstract Refinement 
-----------------------------------------------------------------------


ifoldr = undefined

{- insertSort' :: xs:List a -> {v:IncrList a | size v = size xs} -}







-----------------------------------------------------------------------
-- | 6. But can you prove that you've permuted the input?
-----------------------------------------------------------------------


-- Lets reason about the set of elements in a container

-- measure elems

{-@ predicate EqSize X Y = size X = size Y @-}

-- predicate EqElems


-----------------------------------------------------------------------
-- | Old definitions from 00_Refinements.hs
-----------------------------------------------------------------------

data List a = N | C a (List a)

infixr 9 `C`

{-@ measure size @-}
size          :: List a -> Int
size (C x xs) = 1 + size xs 
size N        = 0

foldr f acc N        = acc
foldr f acc (C x xs) = f x (foldr f acc xs)
 
