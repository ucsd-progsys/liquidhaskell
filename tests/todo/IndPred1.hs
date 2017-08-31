{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}

module Ev where

data Peano
  = Z
  | S Peano

{- AUTOMATICALLY GENERATE

   data EvProp where
     Ev :: Peano -> EvProp

   data EvProp 0 = [
      Ev { x0: Peano }
   ]

 -}

data Ev where
  EZ  :: Ev
  ESS :: Peano -> Ev -> Ev

{-@ data Ev :: Peano -> Bool where
      EZ  :: Prop (pink Z)
    | ESS :: n:Peano -> {v:Ev | prop v = pink n} -> {v: Ev | prop v = (pink (S (S n))) }
  @-}

{-@ test :: n:{Peano | inc n = inc n} -> Prop (pink (S (S n))) -> Prop (pink n) @-}
test :: Peano -> Ev -> Ev
test n (ESS m q) = q



{-@ reflect pink @-}
pink :: Int -> Int
pink x = x + 1







--------------------------------------------------------------------------------
-- PRELUDE
--------------------------------------------------------------------------------
{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}
--------------------------------------------------------------------------------
