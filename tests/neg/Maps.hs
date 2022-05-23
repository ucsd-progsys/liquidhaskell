module Maps where

{-@ prop1 :: x:_ -> y:{_ | y == x} -> TT @-}
prop1 x y = (z == 10)
  where
    m1    = put x 10 emp  
    m2    = put y 20 m1
    z     = get x m2

{-@ prop2 :: x:_ -> y:{_ | y == x} -> TT @-}
prop2 x y = (z == 10)
  where
    m1    = put x 10 emp 
    m2    = put y 20 m1
    z     = get x m2

-----------------------------------------------------------------------

data Map k v = M

{-@ embed Map as Map_t @-}
{-@ measure Map_select :: Map k v -> k -> v @-}
{-@ measure Map_store  :: Map k v -> k -> v -> Map k v @-}

emp :: Map Int Int
emp = undefined   
     
{-@ get :: k:k -> m:Map k v -> {v:v | v = Map_select m k} @-}
get :: k -> Map k v -> v
get = undefined 

{-@ put :: k:k -> v:v -> m:Map k v -> {n:Map k v | n = Map_store m k v} @-}
put :: k -> v -> Map k v -> Map k v
put = undefined 
