{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--extensionality"  @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module FunctorList where

import Prelude hiding (id)

import Proves

{-@ axiomatize id @-}
id :: a -> a
id x = x


-- | Sound example

{-@ fmap_id ::  f:(r -> a) -> g:(r -> a) 
            -> { (\r:r -> (id (f r))) == (\r:r-> (f r)) } @-}
fmap_id :: Arg r => (r -> a) -> (r -> a) ->  Proof
fmap_id f g 
   = ((\r -> id (f r)) =*=! (\r -> f r)) (helper f)
   *** QED 


{-@ helper 
  :: f:(r -> a) -> r:r 
  -> {(id (f r) == f r) 
      } @-} 
helper :: Arg r => (r -> a) -> r -> Proof 
helper f r 
  =   id (f r)
  ==! f r 
  *** QED 
