{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--reflection"     @-}

module FunctorMaybe where

import Prelude hiding (fmap, id) 

import Language.Haskell.Liquid.ProofCombinators

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h

{-@ reflect fmap @-}
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap f x
  | is_Just x  = Just (f (from_Just x))
  | otherwise = Nothing

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ fmap_id' :: {v:Proof | fmap id /= id } @-}
fmap_id' :: Proof
fmap_id' = abstract (fmap id) id fmap_id


{-@ fmap_id :: xs:Maybe a -> {v:Proof | fmap id xs /= id xs } @-}
fmap_id :: Maybe a -> Proof
fmap_id Nothing
  =  fmap id Nothing 
  === Nothing
  === id Nothing
  *** QED 

fmap_id (Just x)
  = fmap id (Just x) 
  === Just (id x)
  === Just x
  === id (Just x)
  *** QED 


-- | Distribution

{-@ fmap_distrib' :: f:(a -> a) -> g:(a -> a)
               -> {v:Proof | fmap  (compose f g) /= compose (fmap f) (fmap g) } @-}
fmap_distrib' :: (a -> a) -> (a -> a) -> Proof
fmap_distrib' f g
  = abstract (fmap  (compose f g)) (compose (fmap f) (fmap g))
       (fmap_distrib f g)


{-@ fmap_distrib :: f:(a -> a) -> g:(a -> a) -> xs:Maybe a
               -> {v:Proof | fmap  (compose f g) xs /= (compose (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: (a -> a) -> (a -> a) -> Maybe a -> Proof
fmap_distrib f g Nothing
  = (compose (fmap f) (fmap g)) Nothing
  === (fmap f) ((fmap g) Nothing)
  === fmap f (fmap g Nothing)
  === fmap f Nothing
  === Nothing
  === fmap (compose f g) Nothing
  *** QED

fmap_distrib f g (Just x)
  = fmap (compose f g) (Just x)
  === Just ((compose f g) x)
  === Just (f (g x))
  === (fmap f) (Just (g x))
  === (fmap f) (fmap g (Just x))
  === (fmap f) ((fmap g) (Just x))
  === (compose (fmap f) (fmap g)) (Just x)
  *** QED


{-@ measure from_Just @-}
from_Just :: Maybe a -> a
{-@ from_Just :: xs:{Maybe a | is_Just xs } -> a @-}
from_Just (Just x) = x

{-@ measure is_Nothing @-}
is_Nothing :: Maybe a -> Bool
is_Nothing Nothing = True
is_Nothing _       = False

{-@ measure is_Just @-}
is_Just :: Maybe a -> Bool
is_Just (Just _) = True
is_Just _        = False

{-@ assume abstract :: f:(a -> b) -> g:(a -> b) -> (x:a -> {v:Proof | f x == g x })
             -> {v:Proof | f == g } @-}
abstract :: (a -> b) -> (a -> b) -> (a -> Proof) -> Proof
abstract _ _ _ = trivial 
