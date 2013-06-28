module spec Data.Set where

embed Data.Set.Set as Set_Set

----------------------------------------------------------------------------------------------
-- | Logical Set Operators: Interpreted "natively" by the SMT solver -------------------------
----------------------------------------------------------------------------------------------

-- | union
measure Set_cup  :: (Data.Set.Set a) -> (Data.Set.Set a) -> (Data.Set.Set a)

-- | intersection
measure Set_cap  :: (Data.Set.Set a) -> (Data.Set.Set a) -> (Data.Set.Set a)

-- | difference
measure Set_dif  :: (Data.Set.Set a) -> (Data.Set.Set a) -> (Data.Set.Set a)

-- | singleton
measure Set_sng  :: a -> (Data.Set.Set a)

-- | emptiness test
measure Set_emp  :: (Data.Set.Set a) -> Prop

-- | membership test
measure Set_mem  :: a -> (Data.Set.Set a) -> Prop

-- | inclusion test
measure Set_sub  :: (Data.Set.Set a) -> (Data.Set.Set a) -> Prop 

---------------------------------------------------------------------------------------------
-- | Refined Types for Data.Set Operations --------------------------------------------------
---------------------------------------------------------------------------------------------

isSubsetOf    :: (Ord a) => x:(Data.Set.Set a) -> y:(Data.Set.Set a) -> {v:Bool | ((Prop v) <=> (Set_sub x y))}
member        :: (Ord a) => x:a -> xs:(Data.Set.Set a) -> {v:Bool | ((Prop v) <=> (Set_mem x xs))}

empty         :: {v:(Data.Set.Set a) | (Set_emp v)}
singleton     :: x:a -> {v:(Data.Set.Set a) | v = (Set_sng x)}
insert        :: (Ord a) => x:a -> xs:(Data.Set.Set a) -> {v:(Data.Set.Set a) | v = (Set_cup xs (Set_sng x))}
delete        :: (Ord a) => x:a -> xs:(Data.Set.Set a) -> {v:(Data.Set.Set a) | v = (Set_dif xs (Set_sng x))}

union         :: Ord a => xs:(Data.Set.Set a) -> ys:(Data.Set.Set a) -> {v:(Data.Set.Set a) | v = (Set_cup xs ys)}
intersection  :: Ord a => xs:(Data.Set.Set a) -> ys:(Data.Set.Set a) -> {v:(Data.Set.Set a) | v = (Set_cap xs ys)}
difference    :: Ord a => xs:(Data.Set.Set a) -> ys:(Data.Set.Set a) -> {v:(Data.Set.Set a) | v = (Set_dif xs ys)}


---------------------------------------------------------------------------------------------
-- | The set of elements in a list ----------------------------------------------------------
---------------------------------------------------------------------------------------------

measure listElts :: [a] -> (Data.Set.Set a) 
listElts([])   = {v | (? Set_emp(v))}
listElts(x:xs) = {v | v = (Set_cup (Set_sng x) (listElts xs)) }
