{-@ LIQUID "--reflection" @-} 

{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module T1642A where


{-@ measure eqT :: a -> a -> Bool @-}
{-@ type EqRT a E1 E2 = {v:EqT a | eqT E1 E2} @-}

{-@ eqFun :: f:(a -> b) -> g:(a -> b) 
          -> (x:a -> {v:EqT b | eqT (f x) (g x)}) -> EqRT (a -> b) {f} {g}  @-}
eqFun :: (a -> b) -> (a -> b) -> (a -> EqT b) -> EqT (a -> b)
eqFun = EqFun


{-@ eqSMT :: Eq a => x:a -> y:a -> {v:() | x == y} -> EqRT a {x} {y} @-}
eqSMT :: Eq a => a -> a -> () -> EqT a
eqSMT = EqSMT 

{-@
data EqT :: * -> * where 
   EqSMT  :: Eq a => x:a -> y:a -> {v:() | x == y} -> EqRT a {x} {y}   
   EqFun  :: f:(a -> b) -> g:(a -> b) -> (x:a -> {v:EqT b | eqT (f x) (g x)}) -> EqRT (a -> b) {f} {g}
@-}

data EqT :: * -> *  where 
   EqSMT  :: Eq a => a -> a -> () -> EqT a   
   EqFun  :: (a -> b) -> (a -> b) -> (a -> EqT b) -> EqT (a -> b)  
