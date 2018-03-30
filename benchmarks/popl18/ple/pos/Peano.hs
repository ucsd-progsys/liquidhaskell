{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Peano where

import Prelude hiding (plus)

import Language.Haskell.Liquid.ProofCombinators

-- Why do we need these?
zeroR     :: Peano -> Proof
zeroL     :: Peano -> Proof
plusAssoc :: Peano -> Peano -> Peano -> Proof
plusComm  :: Peano -> Peano -> Proof
plusSuccR :: Peano -> Peano -> Proof


data Peano = Z | S Peano

{-@ data Peano [toInt] @-} 

{-@ measure toInt @-}
toInt :: Peano -> Int

{-@ toInt :: Peano -> Nat @-}
toInt Z     = 0
toInt (S n) = 1 + toInt n

{-@ axiomatize plus @-}
plus :: Peano -> Peano -> Peano
plus Z m     = m
plus (S n) m = S (plus n m)

{-@ zeroL :: n:Peano -> { plus Z n == n }  @-}
zeroL n = trivial 

{-@ zeroR :: n:Peano -> { plus n Z == n }  @-}
zeroR Z     = trivial 
zeroR (S n) = zeroR n

{-@ plusSuccR :: n:Peano -> m:Peano -> { plus n (S m) = S (plus n m) } @-}
plusSuccR Z     _ = trivial
plusSuccR (S n) m = plusSuccR n m

{-@ plusComm :: a:_ -> b:_  -> {plus a b == plus b a} @-}
plusComm Z b = zeroR b
plusComm (S a) b = plusComm a b &&& plusSuccR b a

{-@ plusAssoc :: a:_ -> b:_ -> c:_ -> {plus (plus a b) c == plus a (plus b c) } @-}
plusAssoc Z _ _     = trivial
plusAssoc (S a) b c = plusAssoc a b c
