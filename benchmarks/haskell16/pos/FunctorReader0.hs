{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{- LIQUID "--extensionality"  @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module FunctorList where

import Prelude hiding (fmap, id)

import Proves
import Helper

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h



{-@ axiomatize id @-}
id :: a -> a
id x = x



{-@ fmap_id ::  f:(r -> a) -> g:(r -> a) 
            -> { (\r:r -> (id (f r))) == (\r:r-> (f r)) } @-}
fmap_id :: Arg r => (r -> a) -> (r -> a) ->  Proof
fmap_id f g 
   =   eq_fun (\r -> id (f r)) (\r -> f r) (helper f)



{-@ helper :: f:(r -> a) -> r:r -> {id (f r) == f r} @-} 
helper :: Arg r => (r -> a) -> r -> Proof 
helper f r 
  =   id (f r)
  ==! f r 
  *** QED 
 

{-
r1 :: int 


lam r1 (id (f r1)) == lam r1 (f r1 
-}


class Arg a where 
eq_fun' :: Arg a => (a -> Proof) -> Proof 
{-@ assume eq_fun' :: (x:a -> Proof) -> Proof @-}
eq_fun' = undefined

eq_fun :: Arg a => (a -> b) -> (a -> b) -> (a -> Proof) -> Proof 
{-@ assume eq_fun :: f:(a -> b) -> g:(a -> b) -> (x:a -> {f x == g x}) -> {f == g}@-}
eq_fun = undefined 
{- 
x:a <: r 
x:a |- Proof => f x == g x 

r -> Proof <: x:a -> fx == g x 

-}
{-
forall r. ff r == id (f r)
forall kk. (forall r. kk r == ff r) => (kk == ff)

forall r. gg r == f r 
forall kk. (forall r. kk r == gg r) => (kk == gg)

--- ???--- 

(forall r. id (f r) == f r) && ff == gg 
-}

