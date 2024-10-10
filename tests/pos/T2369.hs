{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE PolyKinds         #-}
{- OPTIONS -fplugin=LiquidHaskellBoot #-}
{-
Cannot add this test in the cabal test because GHC throws the following error:

pos/T2369.hs:14:34: error: [GHC-46956]
    • Couldn't match expected type ‘Proxy cs1’ with actual type ‘t0’
        because type variables ‘k1’, ‘cs1’ would escape their scope
      These (rigid, skolem) type variables are bound by
        an expression type signature:
          forall {k1} (cs1 :: k1). Proxy cs1
        at pos/T2369.hs:14:39-46
    • In the expression: x :: Proxy cs
      In the result of a function call
      In the first argument of ‘tupleToDict’, namely
        ‘(\ x -> x :: Proxy cs)’
    • Relevant bindings include x :: t0 (bound at pos/T2369.hs:14:29)
   |
14 | getMaster _ = tupleToDict (\x -> x :: Proxy cs)
   |
-}

module T2369 where


data Proxy (a :: k) = Proxy

tupleToDict :: p (Proxy cs) -> ()
tupleToDict _ = ()

getMaster :: forall p cs. p cs -> ()
getMaster _ = tupleToDict (\x -> x :: Proxy cs)

class ClsOne f where
    metha :: f a a

instance ClsOne (->) where
    metha = \x -> x




class Cls f where
    meth :: f a a
    bar :: f a a -> f a a  

instance Cls (->) where
    meth = \x -> x
    bar _ x = x 
