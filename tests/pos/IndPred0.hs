{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}

module Ev where

data Peano where
  Z :: Peano
  S :: Peano -> Peano

-- AUTO
data EvProp where
  Ev :: Peano -> EvProp

data Ev where
  EZ  :: Ev
  ESS :: Peano -> Ev -> Ev

-- AUTO/PRELUDE
{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-@ data Ev where
      EZ  :: Prop (Ev Z)
    | ESS :: n:Peano -> Prop (Ev n) -> Prop (Ev (S (S n)))
  @-}

{-@ test :: n:Peano -> Prop (Ev (S (S n))) -> Prop (Ev n) @-}
test :: Peano -> Ev -> Ev
test n (ESS m q) = q

-- G := p : {prop p  = Even (S (S n)) /\ prop p = Even (S (S m))}
--        ; q : {prop q = Even m}
--        ==> n = m
--        ==> prop q = Even n
