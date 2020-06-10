module Language.Haskell.Liquid.Bag where

import qualified Data.Map      as M

{-@ embed   Data.Map.Map as Map_t                                         @-}

{-@ measure Map_default :: Int -> Bag a                                   @-}
{-@ measure Map_union   :: Bag a -> Bag a -> Bag a                        @-}
{-@ measure Map_select  :: Data.Map.Map k v -> k -> v                     @-}
{-@ measure Map_store   :: Data.Map.Map k v -> k -> v -> Data.Map.Map k v @-}
{-@ measure bagSize     :: Bag k -> Int                                   @-}

-- if I just write measure fromList the measure definition is not imported
{-@ measure fromList :: [k] -> Bag k
fromList ([])   = (Map_default 0)
fromList (x:xs) = Map_store (fromList xs) x (1 + (Map_select (fromList xs) x))
@-}


type Bag a = M.Map a Int

{-@ assume empty :: {v:Bag k | v = Map_default 0} @-}
empty :: Bag k
empty = M.empty

{-@ assume bagSize :: b:Bag k -> {i:Nat | i == bagSize b} @-}
bagSize :: Bag k -> Int 
bagSize b = sum (M.elems b) 

{-@ fromList :: (Ord k) => xs:[k] -> {v:Bag k | v == fromList xs } @-} 
fromList :: (Ord k) => [k] -> Bag k 
fromList []     = empty
fromList (x:xs) = put x (fromList xs)

{-@ assume get :: (Ord k) => k:k -> b:Bag k -> {v:Nat | v = Map_select b k}  @-}
get :: (Ord k) => k -> Bag k -> Int
get k m = M.findWithDefault 0 k m

{-@ assume put :: (Ord k) => k:k -> b:Bag k -> {v:Bag k | v = Map_store b k (1 + (Map_select b k))} @-}
put :: (Ord k) => k -> Bag k -> Bag k
put k m = M.insert k (1 + get k m) m

{-@ assume union :: (Ord k) => m1:Bag k -> m2:Bag k -> {v:Bag k | v = Map_union m1 m2} @-}
union :: (Ord k) => Bag k -> Bag k -> Bag k
union m1 m2 = M.union m1 m2

{-@ thm_emp :: x:k -> xs:Bag k ->  { Language.Haskell.Liquid.Bag.empty /= put x xs }  @-}
thm_emp :: (Ord k) => k -> Bag k -> ()  
thm_emp x xs = const () (get x xs)

{-@ assume thm_size :: xs:[k] ->  { bagSize (fromList xs) == len xs }  @-}
thm_size :: (Ord k) => [k] -> ()  
thm_size _ = () 
