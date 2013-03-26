module spec Data.Set where

embed Set as Set_Set

----------------------------------------------------------------------------------------------
-- | Logical Set Operators: Interpreted "natively" by the SMT solver -------------------------
----------------------------------------------------------------------------------------------

-- | union
measure Set_cup  :: (Set a) -> (Set a) -> (Set a)

-- | intersection
measure Set_cap  :: (Set a) -> (Set a) -> (Set a)

-- | difference
measure Set_dif  :: (Set a) -> (Set a) -> (Set a)

-- | singleton
measure Set_sng  :: a -> (Set a)

-- | emptiness test
measure Set_emp  :: (Set a) -> Prop

-- | membership test
measure Set_mem  :: a -> (Set a) -> Prop

-- | inclusion test
measure Set_sub  :: (Set a) -> (Set a) -> Prop 

---------------------------------------------------------------------------------------------
-- | Refined Types for Data.Set Operations --------------------------------------------------
---------------------------------------------------------------------------------------------

isSubsetOf    :: (Ord a) => x:(Set a) -> y:(Set a) -> {v:Bool | ((Prop v) <=> (Set_sub x y))}
member        :: (Ord a) => x:a -> xs:(Set a) -> {v:Bool | ((Prop v) <=> (Set_mem x xs))}

empty         :: {v:(Set a) | (Set_emp v)}
singleton     :: x:a -> {v:(Set a) | v = (Set_sng x)}
insert        :: (Ord a) => x:a -> xs:(Set a) -> {v:(Set a) | v = (Set_cup xs (Set_sng x))}
delete        :: (Ord a) => x:a -> xs:(Set a) -> {v:(Set a) | v = (Set_dif xs (Set_sng x))}

union         :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = (Set_cup xs ys)}
intersection  :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = (Set_cap xs ys)}
difference    :: Ord a => xs:(Set a) -> ys:(Set a) -> {v:(Set a) | v = (Set_dif xs ys)}


---------------------------------------------------------------------------------------------
-- | The set of elements in a list ----------------------------------------------------------
---------------------------------------------------------------------------------------------

measure listElts :: [a] -> (Set a) 
listElts([])   = {v | (? Set_emp(v))}
listElts(x:xs) = {v | v = (Set_cup (Set_sng x) (listElts xs)) }
