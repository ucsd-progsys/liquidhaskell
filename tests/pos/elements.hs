{-@ LIQUID "--pruneunsorted" @-}
module Elems where

import Prelude hiding (elem)

import Data.Set (Set (..))

{-@ append  :: xs:_ -> ys:_ -> {v:_ | UnElts v xs ys} @-}  
append [] ys     = ys
append (x:xs) ys = x : append xs ys 


{-@ reverse :: xs:_ -> {v:_ | EqElts v xs} @-}
reverse xs           = revAcc xs []
  where 
   revAcc []     acc = acc
   revAcc (x:xs) acc = revAcc xs (x:acc)



{-@ nub :: (Eq a) => xs:_ -> {v:_ | nodups v && EqElts v xs} @-}
nub xs             = go xs []
  where
    go (x:xs) l
      | x `elem` l = go xs l     
      | otherwise  = go xs (x:l) 
    go [] l        = l


{-@ elem :: (Eq a) => x:_ -> ys:_ -> {v:Bool | Prop v <=> Set_mem x (elems ys)} @-}
elem x []     = False
elem x (y:ys) = x == y || elem x ys



{-@ find :: (Eq a) => key:_ -> {map:_ | ValidKey key map} -> b @-}  
find key ((k,v):kvs)
  | key == k  = v
  | otherwise = find key kvs
find _ []     = die "Lookup failed!"



{-@ die :: {v:String | false} -> b @-}
die x = error x

----------------------------------------------------------------------------
----------------------------------------------------------------------------
----------------------------------------------------------------------------

{-@ predicate ValidKey K M    = Set_mem K (keys M)                       @-}
{-@ predicate EqElts Xs Ys    = elems Xs = elems Ys                      @-}
{-@ predicate UnElts Xs Ys Zs = elems Xs = Set_cup (elems Ys) (elems Zs) @-}

{-@ measure keys  :: [(a, b)] -> (Set a)
    keys ([])     = (Set_empty 0)
    keys (kv:kvs) = (Set_cup (Set_sng (fst kv)) (keys kvs))
  @-}
 
{-@ measure elems :: [a] -> (Set a)
    elems ([])    = (Set_empty 0)
    elems (x:xs)  = (Set_cup (Set_sng x) (elems xs))
  @-}

{-@ measure nodups :: [a] -> Prop
    nodups ([])   = true
    nodups (x:xs) = (not (Set_mem x (elems xs)) && nodups xs)
  @-}
