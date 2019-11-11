{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--rankNTypes" @-}
{-# LANGUAGE RankNTypes   #-}

module Theorems where

import Language.Haskell.Liquid.Equational 

type ForAll a  = forall z. a
data Wrapper a = Wrapper (ForAll a)
 

{-@ unsound :: ForAll a -> {v:ForAll a | false } @-}
unsound :: ForAll a -> ForAll a 
unsound x = x 
 
