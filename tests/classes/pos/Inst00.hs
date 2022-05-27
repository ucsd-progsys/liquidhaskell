-- TAG: instances 

-- | Typing class-instances  

module Inst00 where

-- | Step 1: Refine type dictionaries:

class Compare a where
	cmax :: a -> a -> a
	cmin :: a -> a -> a

instance Compare Int where
{-@ instance Compare Int where
        cmax :: Odd -> Odd -> Odd ;
        cmin :: Int -> Int -> Int
  @-}

  cmax y x = if x >= y then x else y
  cmin y x = if x >= y then x else y

-- | creates dictionary environment:
-- | * add the following environment
-- | dictionary $fCompareInt :: Compare Int
-- |               { $ccmax :: Odd -> Odd -> Odd
-- |               , $ccmin :: Int -> Int -> Int
-- |               }
-- |
-- | Important: do not type dictionaries, as preconditions
-- | of fields cannot be satisfied!!!!!


-- | Dictionary application 
-- | ((cmax Int)    @fcompareInt) :: Odd -> Odd -> Odd
-- | ((cmin Int)    @fcompareInt) :: Int -> Int -> Int
-- | (anything_else @fcompareInt) :: default


{-@ foo :: Odd -> Odd -> Odd @-}
foo :: Int -> Int -> Int
foo x y = cmax x y 
