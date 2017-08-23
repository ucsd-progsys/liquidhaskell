{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exactdc"        @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectClient7 where

import ReflectLib7 

import Language.Haskell.Liquid.ProofCombinators

data U1 p = U1

{-@ axiomatize fmapU1 @-}
fmapU1 :: (p -> q) -> U1 p -> U1 q
fmapU1 _ _ = U1

{-@ fmapU1Compose :: f:(q -> r)
                  -> g:(p -> q)
                  -> x:U1 p
                  -> { fmapU1 (compose f g) x == compose (fmapU1 f) (fmapU1 g) x }
@-}
fmapU1Compose :: (q -> r) -> (p -> q)
              -> U1 p -> Proof
fmapU1Compose f g x
  = trivial 

  -- =   fmapU1 (compose f g) x
  -- ==. U1
  -- ==. fmapU1 f (fmapU1 g x)
  -- ==. compose (fmapU1 f) (fmapU1 g) x
  -- *** QED
