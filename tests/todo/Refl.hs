{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs"   @-}

module Peano where

import ProofCombinators

{-@ axiomatize incr @-}
incr :: Int -> Int
incr x = x + 1

{-@ pf :: () -> { incr 2 == 3 }  @-}
pf () = incr 2 *** QED



pf :: () -> Proof
