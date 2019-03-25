-- 1. What is a bool asynch rule?
-- 2. Are the {}1 and {}2 attached to the 1st and 2nd options?
-- 3. Should my simpleTake actually fail?

module Take where 

import Prelude hiding (take)
import Relational


data List a = Nil | Cons a (List a)

{-@ Nil :: {xs:List a | llen xs == 0  && llen {xs}1 == 0 && llen {xs}2 == 0 } @-}
{-@ Cons :: x:a -> xs:List a ->  {zs:List a | llen zs == 1 + len xs  && llen {zs}1 == 1 + llen {xs}1  && llen {zs}2 == 1 + llen {xs}2 } @-}
{-@ measure llen :: List a -> Nat  @-}


{-

G |= {e}1 <=> {e}2 
G, e, {e}1, {e}2             |- e1 :: t 
G, not e, {not e}1, {not e}2 |- e2 :: t 
--------------------------------- Sync 
G |- if e then e1 else e2 :: t 


?????
--------------------------------- ASync 
G |- if e then e1 else e2 :: t 


-}


takeSimpl :: Int -> Int 
{-@ takeSimpl :: i:Nat 
         -> {o:Int | {i}1 <= {i}2 => {o}1 == {o}2 } @-}
takeSimpl i = case i of 
    0 -> zero 
    j -> one `plus` (takeSimpl (j `minus` one))  
         -- {o}1 = 1 + {i}1 
         -- {o}2 = 1 + {i}2 
         -- ??[2] why fails?
         -- what is the async here? what if I had more than 2 indices?


