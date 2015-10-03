module Arrow where

data Arrow a b = Arr {runFun :: a -> b}
{-@ measure runFun :: Arrow a b ->  a -> b  @-}
{-@ runFun :: f:Arrow a b-> x:a -> {v:b | v = runFun f x } @-}
