{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{- LIQUID "--extensionality"  @-}


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
   = eq_fun (\r -> id (f r)) (\r -> f r) (helper f)



-- The b-reduction proof obligations are automatically discarded in fixpoint serialize
-- but are required as eq_fun requires a proof that `f r = g r` with 
-- f == \r -> id (f r), and 
-- g == \r -> f r

{-@ helper 
  :: f:(r -> a) -> r:r 
  -> {(id (f r) == f r) 
      && ((\r:r -> (id (f r))) (r) == id (f r))  
      && ((\r:r-> (f r)) (r) == f r) 
      } @-} 
helper :: Arg r => (r -> a) -> r -> Proof 
helper f r 
  =   id (f r)
  ==! f r 
  *** QED 

-- Function equality can be decided only by the following function
-- Add it into the library BUT the argument is guarded by a class predicate, 
-- otherwise because of ocntravariance it is refined to false leading to the 
-- following unsound example

eq_fun :: Arg a => (a -> b) -> (a -> b) -> (a -> Proof) -> Proof 
{-@ assume eq_fun :: f:(a -> b) -> g:(a -> b) 
  -> (r:a -> {f r == g r}) -> {f == g}@-}
eq_fun = undefined 



{-@ fmap_id' ::  f:(r -> a) -> g:(r -> a) 
            -> { (\r:r -> (id (f r))) == (\r:r-> (g r)) } @-}
fmap_id' :: (r -> a) -> (r -> a) ->  Proof
fmap_id' f g 
   = eq_fun' (\r -> id (f r)) (\r -> g r) (\_ -> simpleProof)




eq_fun' :: (a -> b) -> (a -> b) -> (a -> Proof) -> Proof 
{-@ assume eq_fun' :: f:(a -> b) -> g:(a -> b) 
  -> (r:a -> {f r == g r}) -> {f == g}@-}
eq_fun' = undefined 

