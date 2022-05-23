{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--rankNTypes" @-}
{-# LANGUAGE RankNTypes   #-}

module T1555 where

import Language.Haskell.Liquid.Equational 

type ForAll a  = forall z. a
data Wrapper a = Wrapper (ForAll a)
 
foo :: ForAll a -> ForAll a  -> Proof
{-@ foo :: ff:ForAll a -> gg:{ForAll a | ff == gg } -> { Wrapper ff == Wrapper gg } @-} 
foo g f = Wrapper g ==. Wrapper f *** QED 
