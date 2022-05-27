{-@ LIQUID "--reflection"     @-}

module FunctorList where

import Prelude hiding (fmap, id)

import Language.Haskell.Liquid.ProofCombinators 

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h



{-@ reflect fmap @-}
fmap :: (a -> b) -> L a -> L b
fmap f xs
  | llen xs == 0 = N
  | otherwise    = C (f (hd xs)) (fmap f (tl xs))

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)


{-@ fmap_id :: xs:L a -> { fmap id xs == id xs } @-}
fmap_id :: L a -> Proof
fmap_id N
  =   fmap id N 
  === N
  === id N 
  *** QED 
fmap_id (C x xs)
  =  fmap id (C x xs) 
  === C (id x) (fmap id xs)
  === C x (fmap id xs)
    ? fmap_id (xs)
  === C x (id xs)            
  === C x xs
  === id (C x xs)
  *** QED 


-- | Distribution

{-@ fmap_distrib :: f:(a -> a) -> g:(a -> a) -> xs:L a
               -> {v:Proof | fmap  (compose f g) xs == (compose (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: (a -> a) -> (a -> a) -> L a -> Proof
fmap_distrib f g N
  = (compose (fmap f) (fmap g)) N
  === (fmap f) ((fmap g) N)
  === fmap f (fmap g N)
  === fmap f N
  === N
  === fmap (compose f g) N
  *** QED

fmap_distrib f g (C x xs)
  = fmap (compose f g) (C x xs)
  === C ((compose f g) x) (fmap (compose f g) xs)
    ? fmap_distrib f g xs
  === C ((compose f g) x) ((compose (fmap f) (fmap g)) xs) 
  === C ((compose f g) x) (fmap f (fmap g xs))
  === C (f (g x)) (fmap f (fmap g xs))
  === fmap f (C (g x) (fmap g xs))
  === (fmap f) (C (g x) (fmap g xs))
  === (fmap f) (fmap g (C x xs))
  === (fmap f) ((fmap g) (C x xs))
  === (compose (fmap f) (fmap g)) (C x xs)
  *** QED 

data L a = N | C a (L a)
{-@ data L [llen] @-}

{-@ measure nill @-}
nill :: L a -> Bool
nill N = True
nill _ = False

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen N        = 0
llen (C _ xs) = 1 + llen xs

{-@ measure hd @-}
{-@ hd :: {v:L a | llen v > 0 } -> a @-}
hd :: L a -> a
hd (C x _) = x


{-@ measure tl @-}
{-@ tl :: xs:{L a | llen xs > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a
tl (C _ xs) = xs
