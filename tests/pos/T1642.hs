{-@ LIQUID "--reflection" @-} 
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Foo where 
 
data A  :: * -> *  where 
   A  :: Eq a => a -> () -> A a 
 