{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module FunctorList where

import Prelude hiding (fmap, id)

import Proves
-- import Helper

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




{-@ fmap_id ::  x:Reader r a 
            -> { fmap id x == id x } @-}
fmap_id :: (Arg r) => Reader r a ->  Proof
fmap_id x@(Reader f) 
   =   fmap id (Reader f) 
   ==! Reader (\r -> id (f r)) 
   ==! Reader (\r -> f r) ? fmap_id_helper1 x
   ==! Reader f           ? fmap_id_helper2 x 
   ==! id (Reader f) 
   *** QED 



{-@ fmap_id_helper2 ::  x:Reader r a 
            -> { (fromReader x) == (\r:r-> ((fromReader x) (r))) } @-}
fmap_id_helper2 :: (Arg r) => Reader r a ->  Proof
fmap_id_helper2 x@(Reader f) 
   =   ((fromReader x) 
   =*=! (\r -> fromReader x r)) (helper2 x)
   *** QED 

{-@ helper2 :: x:Reader r a  
            -> r:r -> {(fromReader x) (r) == (\r:r-> ((fromReader x) (r))) (r)}
  @-}

helper2 :: Arg r => Reader r a -> r -> Proof
helper2 _ _ = simpleProof 


{-@ fmap_id_helper1 ::  x:Reader r a 
            -> { (\r:r -> (id (fromReader x r))) == (\r:r-> ((fromReader x) (r))) } @-}
fmap_id_helper1 :: (Arg r) => Reader r a ->  Proof
fmap_id_helper1 x@(Reader f) 
   =    ((\r -> id (fromReader x r)) 
   =*=! (\r -> fromReader x r)) (helper x)
   *** QED 



{-@ helper 
  :: f:(Reader r a) -> r:r 
  -> {(id (fromReader f r) == fromReader f r) 
      && ((\r:r -> (id (fromReader f r))) (r) == id (fromReader f r))  
      && ((\r:r-> (fromReader f r)) (r) == fromReader f r) 
      } @-} 
helper :: Arg r => (Reader r a) -> r -> Proof 
helper f r 
  =   id (fromReader f r)
  ==! fromReader f r 
  *** QED 



{-@ measure fromReader @-}
fromReader :: Reader r a -> r -> a
fromReader (Reader f) = f

{-@ qual :: f:(r -> a) -> {v:Reader r a | v == Reader f} @-}
qual :: (r -> a) -> Reader r a 
qual = Reader 