{-# LANGUAGE RankNTypes          #-}

module Foo where 

{-@ LIQUID "--reflection" @-}

import Language.Haskell.Liquid.Equational 

{-@ example :: g:(b -> d) -> p:(a,b) -> { snd (second g p) == g (snd p) } @-}
example :: (b -> d) -> (a,b) -> Proof 
example g p 
  =   snd (second g p) 
  ==. (snd . second g) p 
      ? hFun g
  ==. (g . snd) p 
  ==. g (snd p)
  *** QED 

hFun :: (b -> d) -> Proof 
{-@ hFun :: g:(b -> d) -> { snd . second g == g . snd } @-} 
hFun g = undefined 

{-@ reflect second @-}
second :: (b -> d) -> (forall a. (a,b) -> (a,d))
second g (a,b) = (a, g b)
