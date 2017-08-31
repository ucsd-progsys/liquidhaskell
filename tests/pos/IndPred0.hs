{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}

module Ev where

{-@ data Peano [toNat] @-}
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

{-@ reflect isEven @-}
isEven :: Peano -> Bool 
isEven Z         = True 
isEven (S Z)     = False 
isEven (S (S n)) = isEven n 

{-@ measure toNat         @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int 
toNat Z     = 0 
toNat (S n) = 1 + toNat n 

-- G := p : {prop p  = Even (S (S n)) /\ prop p = Even (S (S m))}
--        ; q : {prop q = Even m}
--        ==> n = m
--        ==> prop q = Even n
