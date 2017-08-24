{-# LANGUAGE GADTs #-}

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

{-@ data Ev where
      EZ  :: {v:Ev | prop v = Ev Z}
    | ESS :: n:Peano -> {v:Ev | prop v = Ev n} -> {v:Ev | prop v = Ev (S (S n)) }
  @-}

{- test :: n:Peano -> {v:Ev | prop v = Ev (S (S n))} -> {v:Ev | prop v = Ev n} @-}
test :: Peano -> Ev -> Ev
test n (ESS m q) = q




-- G := p : {prop p  = Even (S (S n)) /\ prop p = Even (S (S m))}
--        ; q : {prop q = Even m}
--        ==> n = m
--        ==> prop q = Even n
