{-@ LIQUID "--reflection"     @-}

module FunctorMaybe where

import Prelude hiding (fmap, id) 

import Language.Haskell.Liquid.ProofCombinators 

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h

{-@ reflect fmap @-}
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap f Nothing  = Nothing
fmap f (Just x) = Just (f x)

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)


{-@ fmap_id :: xs:Maybe a -> { fmap id xs == id xs } @-}
fmap_id :: Maybe a -> Proof
fmap_id Nothing
  =   fmap id Nothing
  === id Nothing
  *** QED
fmap_id (Just x)
  = fmap id (Just x)
  === Just (id x)
  === id (Just x)
  *** QED


-- | Distribution


{-@ fmap_distrib :: f:(b -> c) -> g:(a -> b) -> xs:Maybe a
               -> { fmap  (compose f g) xs == (compose (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: (b -> c) -> (a -> b) -> Maybe a -> Proof
fmap_distrib f g Nothing
  =
      (compose (fmap f) (fmap g)) Nothing
        === (fmap f) ((fmap g) Nothing)
        === fmap f (fmap g Nothing)
        === fmap f Nothing
        === Nothing
        === fmap (compose f g) Nothing
        *** QED
fmap_distrib f g (Just x)
  =        fmap (compose f g) (Just x)
       === Just ((compose f g) x)
       === Just (f (g x))
       === (fmap f) (Just (g x))
       === (fmap f) (fmap g (Just x))
       === (fmap f) ((fmap g) (Just x))
       === (compose (fmap f) (fmap g)) (Just x)
       *** QED

