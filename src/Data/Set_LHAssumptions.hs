{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.Set_LHAssumptions where

import Data.Set
import GHC.Types_LHAssumptions()

{-@

embed Set as Set_Set

//  ----------------------------------------------------------------------------------------------
//  -- | Logical Set Operators: Interpreted "natively" by the SMT solver -------------------------
//  ----------------------------------------------------------------------------------------------


//  union
measure Set_cup  :: (Set a) -> (Set a) -> (Set a)

//  intersection
measure Set_cap  :: (Set a) -> (Set a) -> (Set a)

//  difference
measure Set_dif   :: (Set a) -> (Set a) -> (Set a)

//  singleton
measure Set_sng   :: a -> (Set a)

//  emptiness test
measure Set_emp   :: (Set a) -> Bool

//  empty set
measure Set_empty :: forall a. Int -> (Set a)

//  membership test
measure Set_mem  :: a -> (Set a) -> Bool

//  inclusion test
measure Set_sub  :: (Set a) -> (Set a) -> Bool

//  ---------------------------------------------------------------------------------------------
//  -- | Refined Types for Data.Set Operations --------------------------------------------------
//  ---------------------------------------------------------------------------------------------

assume isSubsetOf    :: (Ord a) => x:(Set a) -> y:(Set a) -> {v:Bool | v <=> Set_sub x y}
assume Data.Set.Internal.member        :: Ord a => x:a -> xs:(Set a) -> {v:Bool | v <=> Set_mem x xs}
assume Data.Set.Internal.null          :: Ord a => xs:(Set a) -> {v:Bool | v <=> Set_emp xs}

assume Data.Set.Internal.empty         :: {v:(Set a) | Set_emp v}
assume Data.Set.Internal.singleton     :: x:a -> {v:(Set a) | v = (Set_sng x)}
assume Data.Set.Internal.insert        :: Ord a => x:a -> xs:(Set a) -> {v:(Set a) | v = Set_cup xs (Set_sng x)}
assume Data.Set.Internal.delete        :: (Ord a) => x:a -> xs:(Set a) -> {v:(Set a) | v = Set_dif xs (Set_sng x)}

assume Data.Set.Internal.union         :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = Set_cup xs ys}
assume Data.Set.Internal.intersection  :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = Set_cap xs ys}
assume Data.Set.Internal.difference    :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = Set_dif xs ys}

assume Data.Set.Internal.fromList :: Ord a => xs:[a] -> {v:Set a | v = listElts xs}
assume Data.Set.Internal.toList   :: Ord a => s:Set a -> {xs:[a] | s = listElts xs}

//  ---------------------------------------------------------------------------------------------
//  -- | The set of elements in a list ----------------------------------------------------------
//  ---------------------------------------------------------------------------------------------

measure listElts :: [a] -> Set a
  listElts []     = {v | (Set_emp v)}
  listElts (x:xs) = {v | v = Set_cup (Set_sng x) (listElts xs) }

@-}
