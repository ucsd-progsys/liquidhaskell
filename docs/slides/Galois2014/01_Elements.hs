{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{- LIQUID "--smtsolver=cvc4" @-}
module Elems where

import Prelude hiding (elem)

import Data.Set (Set (..))


-----------------------------------------------------------------------------
-- | 1. Reasoning about the Set of Elements in a List ----------------------- 
-----------------------------------------------------------------------------

-- | The set of `elems` of a list





{-@ measure elems :: [a] -> (Set a)
    elems ([])    = (Set_empty 0)
    elems (x:xs)  = (Set_cup (Set_sng x) (elems xs))
  @-}




-- | A few handy aliases

{-@ predicate EqElts Xs Ys    = elems Xs = elems Ys                      @-}
{-@ predicate UnElts Xs Ys Zs = elems Xs = Set_cup (elems Ys) (elems Zs) @-}

-- | Reasoning about `append` and `reverse`

{-@ append  :: xs:_ -> ys:_ -> {v:_ | UnElts v xs ys} @-}  
append [] ys     = ys
append (x:xs) ys = x : append xs ys 


{-@ reverse :: xs:_ -> {v:_ | EqElts v xs} @-}
reverse xs           = revAcc xs []
  where 
   revAcc []     acc = acc
   revAcc (x:xs) acc = revAcc xs (x:acc)




-----------------------------------------------------------------------------
-- | 2. Checking for duplicates (xmonad) ------------------------------------ 
-----------------------------------------------------------------------------

-- | Is a list free of duplicates?
   
{-@ measure nodups :: [a] -> Prop
    nodups ([])   = true
    nodups (x:xs) = (not (Set_mem x (elems xs)) && nodups xs)
  @-}

-- | Weeding out duplicates.
   
{-@ nub :: xs:_ -> {v:_ | nodups v && EqElts v xs} @-}
nub xs             = go xs []
  where
    go (x:xs) l
      | x `elem` l = go xs l     
      | otherwise  = go xs (x:l) 
    go [] l        = l


{-@ elem :: x:_ -> ys:_ -> {v:Bool | Prop v <=> Set_mem x (elems ys)} @-}
elem x []     = False
elem x (y:ys) = x == y || elem x ys

-----------------------------------------------------------------------------
-- | 3. Associative Lookups ------------------------------------------------- 
-----------------------------------------------------------------------------

-- The dread "key-not-found". How can we fix it?
find key ((k,v) : kvs)
  | key == k  = v
  | otherwise = find key kvs
find _ []     = die "Key not found! Lookup failed!"


{-@ die :: {v:_ | false} -> b @-}
die x = error x


----------------------------------------------------------------------------
-- | CHEAT AREA ------------------------------------------------------------
----------------------------------------------------------------------------

{- predicate ValidKey K M    = Set_mem K (keys M)  @-}

{- measure keys  :: [(a, b)] -> (Set a)
    keys ([])     = (Set_empty 0)
    keys (kv:kvs) = (Set_cup (Set_sng (fst kv)) (keys kvs))
  @-}

-- # START ERRORS 1 (find)
-- # END   ERRORS 0 

{- find :: k:_ -> {m:_ | ValidKey k m} -> _ @-}

