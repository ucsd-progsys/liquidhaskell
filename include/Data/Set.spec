module spec Data.Set where

embed Set as Set_Set

measure Set_cup  :: (Set a) -> (Set a) -> (Set a)
measure Set_cap  :: (Set a) -> (Set a) -> (Set a)
measure Set_sub  :: (Set a) -> (Set a) -> Prop 
measure Set_sng  :: a -> (Set a)
measure Set_emp  :: (Set a) -> Prop
measure Set_mem  :: a -> (Set a) -> Prop


measure listElts :: [a] -> (Set a) 
listElts([])   = {v | (? Set_emp(v))}
listElts(x:xs) = {v | v = (Set_cup (Set_sng x) (listElts xs)) }
