{-# LANGUAGE NoImplicitPrelude #-}
{- OPTIONS -fplugin=LiquidHaskellBoot #-}
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
