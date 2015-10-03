module Arrow where

data Arrow a b = Arr {runFun :: a -> b}
{-@ measure runFun :: Arrow a b ->  a -> b  @-}
