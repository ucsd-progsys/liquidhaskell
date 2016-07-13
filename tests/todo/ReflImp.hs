{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs"   @-}

module Peano where

import ProofCombinators

import Incr (incr)

{-@ pf :: () -> { incr 2 == 3 }  @-}
pf () = incr 2 *** QED




pf :: () -> Proof
