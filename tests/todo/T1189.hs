

{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple"            @-}

module Ev where

data Peano where
  Z :: Peano

{-@ reflect plus @-}
plus :: Peano -> Peano -> Peano
plus Z Z = Z

data EvProp where
  Ev :: Peano -> EvProp

data Ev where
  EZ  :: Ev

{-@ data Ev where
      EZ  :: Prop (Ev Z)
  @-}

{-@ ev_sum :: n:Peano -> Prop (Ev n) -> Prop (Ev (plus n n)) @-}
ev_sum :: Peano -> Ev -> Ev
ev_sum Z pf = pf

--------------------------------------------------------------------------------
-- | Syntactic sugar for prelude -----------------------------------------------
--------------------------------------------------------------------------------
{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}
