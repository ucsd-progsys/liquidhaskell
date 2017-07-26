{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Peano where

data Peano = Z | S {prev :: Peano}
{-@ data Peano = Z | S {prev :: Peano} @-}

{-@ test :: n:Peano -> m:Peano -> { v:() | S n == S m } -> { n == m } @-}
test :: Peano -> Peano -> () -> ()
test _ _ _ = ()
