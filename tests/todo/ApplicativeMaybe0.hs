{-@ LIQUID "--higherorder"     @-}
{- LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{-@ LIQUID "--fuel=10" @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module ListFunctors where

import MaybeReflect0 
import Prelude hiding (Maybe(..))
import Language.Haskell.Liquid.ProofCombinators


{-

liquid: liquid: panic! (the 'impossible' happened)
  (GHC version 7.10.3 for x86_64-apple-darwin):
  lookupRdrNameInModule

Please report this as a GHC bug:  http://www.haskell.org/ghc/reportabug

-}


{-@ composition :: x:Maybe (a -> a)
                -> y:Maybe (a -> a)
                -> z:Maybe a
                -> { seq x (seq y z)  = seq x (seq y z) } @-}
composition :: Maybe (a -> a) -> Maybe (a -> a) -> Maybe a -> Proof
composition = undefined 



