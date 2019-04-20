module spec Data.Set where

embed Data.Set.Internal.Set as Set_Set

// ----------------------------------------------------------------------------------------------
// -- | Logical Set Operators: Interpreted "natively" by the SMT solver -------------------------
// ----------------------------------------------------------------------------------------------


// union
measure Set_cup  :: (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a)

// intersection
measure Set_cap  :: (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a)

// difference
measure Set_dif   :: (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a)

// singleton
measure Set_sng   :: a -> (Data.Set.Internal.Set a)

// emptiness test
measure Set_emp   :: (Data.Set.Internal.Set a) -> GHC.Types.Bool

// empty set
measure Set_empty :: forall a. GHC.Types.Int -> (Data.Set.Internal.Set a)

// membership test
measure Set_mem  :: a -> (Data.Set.Internal.Set a) -> GHC.Types.Bool

// inclusion test
measure Set_sub  :: (Data.Set.Internal.Set a) -> (Data.Set.Internal.Set a) -> GHC.Types.Bool

// ---------------------------------------------------------------------------------------------
// -- | Refined Types for Data.Set Operations --------------------------------------------------
// ---------------------------------------------------------------------------------------------

isSubsetOf    :: (GHC.Classes.Ord a) => x:(Data.Set.Internal.Set a) -> y:(Data.Set.Internal.Set a) -> {v:GHC.Types.Bool | v <=> Set_sub x y}
member        :: (GHC.Classes.Ord a) => x:a -> xs:(Data.Set.Internal.Set a) -> {v:GHC.Types.Bool | v <=> Set_mem x xs}
null          :: (GHC.Classes.Ord a) => xs:(Data.Set.Internal.Set a) -> {v:GHC.Types.Bool | v <=> Set_emp xs}

empty         :: {v:(Data.Set.Internal.Set a) | Set_emp v}
singleton     :: x:a -> {v:(Data.Set.Internal.Set a) | v = (Set_sng x)}
insert        :: (GHC.Classes.Ord a) => x:a -> xs:(Data.Set.Internal.Set a) -> {v:(Data.Set.Internal.Set a) | v = Set_cup xs (Set_sng x)}
delete        :: (GHC.Classes.Ord a) => x:a -> xs:(Data.Set.Internal.Set a) -> {v:(Data.Set.Internal.Set a) | v = Set_dif xs (Set_sng x)}

union         :: GHC.Classes.Ord a => xs:(Data.Set.Internal.Set a) -> ys:(Data.Set.Internal.Set a) -> {v:(Data.Set.Internal.Set a) | v = Set_cup xs ys}
intersection  :: GHC.Classes.Ord a => xs:(Data.Set.Internal.Set a) -> ys:(Data.Set.Internal.Set a) -> {v:(Data.Set.Internal.Set a) | v = Set_cap xs ys}
difference    :: GHC.Classes.Ord a => xs:(Data.Set.Internal.Set a) -> ys:(Data.Set.Internal.Set a) -> {v:(Data.Set.Internal.Set a) | v = Set_dif xs ys}

fromList :: GHC.Classes.Ord a => xs:[a] -> {v:Data.Set.Internal.Set a | v = listElts xs}

// ---------------------------------------------------------------------------------------------
// -- | The set of elements in a list ----------------------------------------------------------
// ---------------------------------------------------------------------------------------------

measure listElts :: [a] -> (Data.Set.Internal.Set a)
listElts([])   = {v | (Set_emp v)}
listElts(x:xs) = {v | v = Set_cup (Set_sng x) (listElts xs) }
