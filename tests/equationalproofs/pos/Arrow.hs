module Arrow where

data Arrow a b = Arr {runFun :: a -> b}
