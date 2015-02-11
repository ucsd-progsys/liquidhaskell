{-@ LIQUID "--short-names"    @-}
module Foo where

data List a = N | C a (List a)


{-@ crashC :: forall a b <p :: List a -> b -> Prop>.
               x:a -> xs: List a 
               -> ys:b<p (C x xs)> 
               -> b<p ys>                            @-}
crashC :: a -> List a -> b -> b 
crashC = undefined


{-@ crashN :: forall a b <p :: List a -> b -> Prop>.
               x:a -> xs: List a 
               -> ys:b<p N> 
               -> b<p ys>                            @-}
crashN :: a -> List a -> b -> b 
crashN = undefined


-- Currenlty the liternals are grapped only from the haskell code
-- and not from the types. 
-- Thus the above two specifications cash unless
-- N and C appear in the Haskell code, as below 

{-
cons :: a -> List a -> List a
cons = C 

nil :: List a 
nil = N
-}
