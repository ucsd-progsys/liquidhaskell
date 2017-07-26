{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Peano  where

import Language.Haskell.Liquid.ProofCombinators

data Peano = Z | S {prev :: Peano}
{-@ data Peano = Z | S {prev :: Peano} @-}

{-@ measure minus @-}
minus :: Peano -> Peano
minus (S n) = n
minus Z     = Z

{-@ test :: n:Peano -> m:Peano -> { v:() | S n == S m } -> { n == m } @-}
test :: Peano -> Peano -> () -> ()
test n m pf = minus (S n) ==. minus (S m) *** QED
