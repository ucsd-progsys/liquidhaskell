{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}

-- Natural transformation 

 {-@ infixr 1 ==> @-} 
 infixr 1 ==> 
 type f ==> g = forall z. f z -> g z 
  


 naturality :: (Functor f, Functor g) => (f ==> g) -> (q -> r) -> f q -> () 
 {-@ naturality :: g:(f ==> g) -> h:(q -> r) -> p:f q 
                       -> { true } @-} 
 naturality _ _ _ = () 
