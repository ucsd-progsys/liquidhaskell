{-@ LIQUID "--reflection" @-} 

{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module RefinedEquality where 


{-@ measure eqT :: a -> a -> Bool @-}
{-@ type EqRT a E1 E2 = {v:EqT a | eqT E1 E2} @-}


{-@ eqSMT :: Eq a => w:a -> x:a -> y:a -> {v:() | x == y} -> EqRT a {x} {w} @-}
eqSMT :: Eq a => a -> a -> a -> () -> EqT a
eqSMT _ = EqSMT 

{-@
data EqT a where 
   EqSMT  :: Eq a => x:a -> y:a -> {v:() | x == y} -> EqRT a {x} {y}   
@-}

data EqT  :: * -> *  where 
   EqSMT  :: Eq a => a -> a -> () -> EqT a   
