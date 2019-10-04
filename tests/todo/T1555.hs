{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--rankNTypes" @-}
{-# LANGUAGE RankNTypes   #-}

module Theorems where

import Language.Haskell.Liquid.Equational 

type ForAll a  = forall z. a
data Wrapper a = Wrapper (ForAll a)
 
foo :: ForAll a -> ForAll a  -> Proof
{-@ foo :: f:ForAll a -> g:{ForAll a | f == g }  -> { Wrapper f == Wrapper g } @-} 
foo g f = Wrapper g ==. Wrapper f *** QED 


{-@ unsound :: ForAll a -> {v:ForAll a | false } @-}
unsound :: ForAll a -> ForAll a 
unsound x = x 

 
