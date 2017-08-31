{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Ev where

{-@ data Peano [toNat] @-}
data Peano where
  Z :: Peano
  S :: Peano -> Peano

data EvProp where
  Ev :: Peano -> EvProp

data Ev where
  EZ  :: Ev
  ESS :: Peano -> Ev -> Ev

{-@ data Ev [evNat] where
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

{-@ thm1 :: n:{Peano | isEven n} -> Prop (Ev n) @-}
thm1 :: Peano -> Ev
thm1 Z         = EZ
thm1 (S (S n)) = ESS n (thm1 n)

{-@ thm2 :: n:Peano -> pf:(Prop (Ev n)) -> {isEven n} / [evNat pf] @-}
thm2 :: Peano -> Ev -> ()
thm2 n EZ         = ()
thm2 n (ESS m pf) = thm2 m pf


--------------------------------------------------------------------------------
-- | Syntactic sugar for prelude -----------------------------------------------
--------------------------------------------------------------------------------

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

--------------------------------------------------------------------------------
-- | Crufty termination stuff [How to auto-generate?] --------------------------
--------------------------------------------------------------------------------

{-@ measure toNat         @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int
toNat Z     = 0
toNat (S n) = 1 + toNat n


{-@ measure evNat      @-}
{-@ evNat :: Ev -> Nat @-}
evNat :: Ev -> Int
evNat EZ        = 0
evNat (ESS _ p) = 1 + evNat p


-- G := p : {prop p  = Even (S (S n)) /\ prop p = Even (S (S m))}
--        ; q : {prop q = Even m}
--        ==> n = m
--        ==> prop q = Even n
