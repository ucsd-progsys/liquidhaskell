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
{-@ measure prop :: a -> b @-}

{-@ type Prop E = {v:_ | pro v = E} @-}

      -- {v:Ev | prop v = Ev Z}
{-@ data Ev where
      EZ  :: Prop (Ev Z)
    | ESS :: evn:Peano -> {evpf:Ev | prop evpf = Ev evn} -> {zing : Ev | prop zing = Ev (S (S evn)) }
  @-}

{-@ test :: n:Peano -> {v:Ev | prop v = Ev (S (S n))} -> {v:Ev | prop v = Ev n} @-}
test :: Peano -> Ev -> Ev
test n (ESS m q) = q

-- G := p : {prop p  = Even (S (S n)) /\ prop p = Even (S (S m))}
--        ; q : {prop q = Even m}
--        ==> n = m
--        ==> prop q = Even n
