module spec Data.Set where

embed Set as Set_Set

measure listElts :: [a] -> Set a 
listElts([])   = {v | (? Set_emp(v))}
listElts(x:xs) = {v | v = Set_cup(Set_sng(x), listElts(xs)) }
