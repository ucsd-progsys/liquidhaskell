{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--higherorderqs"   @-}

module Peano where

import ProofCombinators

import IncrLib (incr)

{-@ pf :: () -> { incr 2 == 3 }  @-}
pf () = incr 2 *** QED




pf :: () -> Proof
