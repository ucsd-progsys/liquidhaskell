module Take where 

import Prelude hiding (take)
import Relational


data List a = Nil | Cons a (List a)

{-@ Nil :: {xs:List a | llen xs == 0  && llen {xs}1 == 0 && llen {xs}2 == 0 } @-}
{-@ Cons :: x:a -> xs:List a ->  {zs:List a | llen zs == 1 + len xs  && llen {zs}1 == 1 + llen {xs}1  && llen {zs}2 == 1 + llen {xs}2 } @-}
{-@ measure llen :: List a -> Nat  @-}

takeSimpl :: Int -> List a -> List a  
{-@ takeSimpl :: i:Nat -> List a 
         -> {os:List a | {i}1 <= {i}2 => llen {os}1 <= llen {os}2 } @-}
takeSimpl i xs = case i of 
    0 -> Nil  
    j -> case xs of 
           Nil -> Nil 
           (Cons y ys) -> Cons y (takeSimpl (j `minus` one) ys)  


