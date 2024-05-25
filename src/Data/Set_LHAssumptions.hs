{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.Set_LHAssumptions where

import Data.Set
import GHC.Types_LHAssumptions()

{-@

embed Data.Set.Internal.Set as Set_Set

//  ----------------------------------------------------------------------------------------------
//  -- | Logical Set Operators: Interpreted "natively" by the SMT solver -------------------------
//  ----------------------------------------------------------------------------------------------


//  union
measure Set_cup  :: (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a)

//  intersection
measure Set_cap  :: (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a)

//  difference
measure Set_dif   :: (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a)

//  singleton
measure Set_sng   :: a -> (Data.Set.Internal.Set a)

//  emptiness test
measure Set_emp   :: (Data.Set.Internal.Set a) -> GHC.Types.Bool

//  empty set
measure Set_empty :: forall a. GHC.Types.Int -> (Data.Set.Internal.Set a)

//  membership test
measure Set_mem  :: a -> (Data.Set.Internal.Set a) -> GHC.Types.Bool

//  inclusion test
measure Set_sub  :: (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a) -> GHC.Types.Bool

//  ---------------------------------------------------------------------------------------------
//  -- | Refined Types for Data.Set Operations --------------------------------------------------
//  ---------------------------------------------------------------------------------------------

assume Data.Set.Internal.isSubsetOf    :: (GHC.Classes.Ord a) => x:(Data.Set.Internal.Set a) -> y:(Data.Set.Internal.Set a) -> {v:GHC.Types.Bool | v <=> Set_sub x y}
assume Data.Set.Internal.member        :: (GHC.Classes.Ord a) => x:a -> xs:(Data.Set.Internal.Set a) -> {v:GHC.Types.Bool | v <=> Set_mem x xs}
assume Data.Set.Internal.null          :: (GHC.Classes.Ord a) => xs:(Data.Set.Internal.Set a) -> {v:GHC.Types.Bool | v <=> Set_emp xs}

assume Data.Set.Internal.empty         :: {v:(Data.Set.Internal.Set a) | Set_emp v}
assume Data.Set.Internal.singleton     :: x:a -> {v:(Data.Set.Internal.Set a) | v = (Set_sng x)}
assume Data.Set.Internal.insert        :: (GHC.Classes.Ord a) => x:a -> xs:(Data.Set.Internal.Set a) -> {v:(Data.Set.Internal.Set a) | v = Set_cup xs (Set_sng x)}
assume Data.Set.Internal.delete        :: (GHC.Classes.Ord a) => x:a -> xs:(Data.Set.Internal.Set a) -> {v:(Data.Set.Internal.Set a) | v = Set_dif xs (Set_sng x)}

assume Data.Set.Internal.union         :: GHC.Classes.Ord a => xs:(Data.Set.Internal.Set a) -> ys:(Data.Set.Internal.Set a) -> {v:(Data.Set.Internal.Set a) | v = Set_cup xs ys}
assume Data.Set.Internal.intersection  :: GHC.Classes.Ord a => xs:(Data.Set.Internal.Set a) -> ys:(Data.Set.Internal.Set a) -> {v:(Data.Set.Internal.Set a) | v = Set_cap xs ys}
assume Data.Set.Internal.difference    :: GHC.Classes.Ord a => xs:(Data.Set.Internal.Set a) -> ys:(Data.Set.Internal.Set a) -> {v:(Data.Set.Internal.Set a) | v = Set_dif xs ys}

assume Data.Set.Internal.fromList :: GHC.Classes.Ord a => xs:[a] -> {v:Data.Set.Internal.Set a | v = listElts xs}
assume Data.Set.Internal.toList   :: GHC.Classes.Ord a => s:Data.Set.Internal.Set a -> {xs:[a] | s = listElts xs}

//  ---------------------------------------------------------------------------------------------
//  -- | The set of elements in a list ----------------------------------------------------------
//  ---------------------------------------------------------------------------------------------

measure listElts :: [a] -> (Data.Set.Internal.Set a)
  listElts []     = {v | (Set_emp v)}
  listElts (x:xs) = {v | v = Set_cup (Set_sng x) (listElts xs) }

@-}
