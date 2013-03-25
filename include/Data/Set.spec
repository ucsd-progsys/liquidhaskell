module spec Data.Set where

embed Set as Set_Set

-- The following operators are interpreted "natively" by the SMT solver

-- | union
measure Set_cup  :: (Set a) -> (Set a) -> (Set a)

-- | intersection
measure Set_cap  :: (Set a) -> (Set a) -> (Set a)

-- | singleton
measure Set_sng  :: a -> (Set a)

-- | emptiness test
measure Set_emp  :: (Set a) -> Prop

-- | membership test
measure Set_mem  :: a -> (Set a) -> Prop

-- | inclusion test
measure Set_sub  :: (Set a) -> (Set a) -> Prop 


-- | The set of elements in a list

measure listElts :: [a] -> (Set a) 
listElts([])   = {v | (? Set_emp(v))}
listElts(x:xs) = {v | v = (Set_cup (Set_sng x) (listElts xs)) }
