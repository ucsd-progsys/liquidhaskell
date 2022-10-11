{-@ LIQUID "--reflection" @-} 
{-@ LIQUID "--ple"        @-} 

module T1634 where

import Language.Haskell.Liquid.ProofCombinators 
type Reader a b = a -> b

data EqT a = EqSMT a a  
   
{-@ assume eqSMT :: x:a -> y:{a | x == y } ->  EqT a @-}
eqSMT :: a -> a -> EqT a
eqSMT = EqSMT

{-@ reflect fmapReader @-}
fmapReader :: (a -> b) -> (r -> a) -> (Reader r b)
fmapReader fab fra r = fab (fra r)

{-@ reflect myid @-}
myid :: a -> a 
myid x = x 

helper2 :: Reader r a -> r -> EqT a
helper2 r a = eqSMT (fmapReader myid r a) (myid (r a))

