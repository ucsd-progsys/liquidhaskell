{-@ LIQUID "--reflection" @-} 
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module T1642 where
 
data A  :: * -> *  where 
   A  :: Eq a => a -> () -> A a 
 
