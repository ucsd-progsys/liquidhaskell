{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--extensionality"  @-}

{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleContexts    #-}
module FunctorList where

import Prelude hiding (fmap, id)

import Proves

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h

{-@ data Reader r a = Reader { runIdentity :: r -> a } @-}
data Reader r a     = Reader { runIdentity :: r -> a }

{-@ axiomatize fmap @-}
fmap :: (a -> b) -> Reader r a -> Reader r b
fmap f (Reader rd) = Reader (\r -> f (rd r))

{-@ axiomatize id @-}
id :: a -> a
id x = x

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

-- | Identity 

{-@ fmap_id :: xs:Reader r a -> { fmap id xs == id xs } @-}
fmap_id :: Arg r => Reader r a  ->  Proof
fmap_id (Reader x) 
   =   fmap id (Reader x)
   ==! Reader (\r -> id (x r))
   ==! Reader (\r -> x r)       ? fmap_id_helper x  
   ==! Reader x                
   ==! id (Reader x)
   *** QED
 

{-@ fmap_id_helper ::  f:(r -> a)
            -> { (\r:r -> (id (f r))) == (\r:r-> (f (r))) } @-}
fmap_id_helper :: (Arg r) => (r -> a) ->  Proof
fmap_id_helper f
   =    ((\r -> id (f r)) 
   =*=! (\r -> f r)) (fmap_id_helper_body f)
   *** QED 


{-@ fmap_id_helper_body 
  :: f:(r -> a) -> r:r 
  -> {(id (f r) == f r) 
      && ((\r:r -> (id (f r))) (r) == id (f r))  
      && ((\r:r-> (f r)) (r) == f r) 
      } @-} 
fmap_id_helper_body :: Arg r => (r -> a) -> r -> Proof 
fmap_id_helper_body f r 
  = id (f r) ==! f r *** QED 



{-@ fmap_distrib :: f:(a -> a) -> g:(a -> a) -> xs:Reader r a
               -> { fmap  (compose f g) xs == (compose (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: Arg r => (a -> a) -> (a -> a) -> Reader r a -> Proof
fmap_distrib f g (Reader x)
  =   fmap (compose f g) (Reader x)
  ==! Reader (\r -> (compose f g) (x r))     
  ==! Reader (\r -> f ( g (x r)))            ? fmap_distrib_helper f g x 
  ==! Reader (\r -> f ((\w -> g (x w)) r))
  ==! fmap f (Reader (\w -> g (x w)))
  ==! fmap f (fmap g (Reader x))
  ==! (compose (fmap f) (fmap g)) (Reader x)
  *** QED





fmap_distrib_helper :: Arg r => (a -> a) -> (a -> a) -> (r -> a) -> Proof 
{-@ fmap_distrib_helper
  :: f:(a -> a) -> g:(a -> a) -> x:(r -> a) 
  -> {(\r:r -> (compose f g) (x r)) == (\r:r -> (f (g (x r))) ) } @-}
fmap_distrib_helper f g x 
  =   ((\r -> (compose f g) (x r)) 
  =*=! (\r -> f (g (x r)))) (fmap_distrib_helper' f g x)
  *** QED 



fmap_distrib_helper' :: Arg r => (a -> a) -> (a -> a) -> (r -> a) -> r -> Proof 
{-@ fmap_distrib_helper' 
  :: f:(a -> a) -> g:(a -> a) -> x:(r -> a) -> r:r
  -> { (compose f g) (x r) == (f (g (x r))) } @-}
fmap_distrib_helper' f g x r  
  =   (compose f g) (x r) 
  ==! f (g (x r))
  *** QED 



{-@ qual :: f:(r -> a) -> {v:Reader r a | v == Reader f} @-}
qual :: (r -> a) -> Reader r a 
qual = Reader 
