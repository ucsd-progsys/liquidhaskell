{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--rankNTypes" @-}

{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Theorems where

import Equational 

data StackFun a b = SF (forall z. (a,z) -> (b,z))


{-@ injectiveProp' :: f:(forall b. (a,b) -> (c,b)) -> f':(forall b. (a,b) -> (c,b)) 
                   -> { SF f == SF f' => f ==  f' } @-}
injectiveProp' :: (forall b. (a,b) -> (c,b)) -> (forall b. (a,b) -> (c,b)) -> ()
injectiveProp' f f'
  =   SF (first f) 
  ==. SF (first f) 
  -*- QED 

{-@ reflect first @-}
first :: (a -> c) -> (forall b. (a,b) -> (c,b))
first f (a,b) = (f a,b)