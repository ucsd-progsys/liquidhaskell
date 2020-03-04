{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}

module T1567 where

 {-@ infixr 1 ==> @-} 
 infixr 1 ==> 
 type f ==> g = forall z. f z -> g z 
  


 test ::  (f ==> g) -> f x -> f y -> ()
 {-@ test :: g:(f ==> g) -> f x -> f y -> ()  @-} 
 test _ _ _ = () 
