{-#LH LIQUID "--higherorder"     @-}
{-#LH LIQUID "--totality"        @-}
{-#LH LIQUID "--exact-data-cons" @-}
{-#LH LIQUID "--higherorderqs" @-}

module Peano where

import Prelude hiding (plus)

-- import Proves

import ProofCombinators

-- Why do we need these?
zeroR     :: Peano -> Proof
zeroL     :: Peano -> Proof
plusAssoc :: Peano -> Peano -> Peano -> Proof
plusComm  :: Peano -> Peano -> Proof
plusSuccR :: Peano -> Peano -> Proof

infixl 3 ==.

(==.) :: a -> a -> a
x ==. _ = x 

data Peano = Z | S Peano

{-#LH data Peano [toInt] = Z | S {prev :: Peano} @-}

{-#LH measure toInt @-}
toInt :: Peano -> Int

{-#LH toInt :: Peano -> Nat @-}
toInt Z     = 0
toInt (S n) = 1 + toInt n

{-#LH axiomatize plus @-}
plus :: Peano -> Peano -> Peano
plus Z m     = m
plus (S n) m = S (plus n m)

{-#LH zeroL :: n:Peano -> { plus Z n == n }  @-}
zeroL n
  =   plus Z n
  ==! n
  *** QED

{-#LH zeroR :: n:Peano -> { plus n Z == n }  @-}
zeroR Z
  = plus Z Z
  ==! Z
  *** QED

zeroR (S n)
  =   plus (S n) Z
  ==! S (plus n Z)
  ==! S n                      ∵ zeroR n
  *** QED

{-#LH plusSuccR :: n:Peano -> m:Peano -> { plus n (S m) = S (plus n m) } @-}
plusSuccR Z m
  =   plus Z (S m)
  ==! S m
  ==! S (plus Z m)
  *** QED

plusSuccR (S n) m
  =   plus (S n) (S m)
  ==! S (plus n (S m))
  ==! S (S (plus n m))        ∵ plusSuccR n m
  ==! S (plus (S n) m)
  *** QED

{-#LH plusComm :: a:_ -> b:_  -> {plus a b == plus b a} @-}
plusComm Z b
  =   plus Z b
  ==! plus b Z                ∵ zeroR b
  *** QED

plusComm (S a) b
  =   plus (S a) b
  ==! S (plus a b)
  ==! S (plus b a)            ∵ plusComm a b
  ==! plus b (S a)            ∵ plusSuccR b a
  *** QED

{-#LH plusAssoc :: a:_ -> b:_ -> c:_ -> {plus (plus a b) c == plus a (plus b c) } @-}
plusAssoc Z b c
  =   plus (plus Z b) c
  ==! plus b c
  ==! plus Z (plus b c)
  *** QED

plusAssoc (S a) b c
  =   plus (plus (S a) b) c
  ==! plus (S (plus a b)) c
  ==! S (plus (plus a b) c)
  ==! S (plus a (plus b c))   ∵ plusAssoc a b c
  ==! plus (S a) (plus b c)
  *** QED
