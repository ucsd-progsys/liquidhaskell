{-@ LIQUID "--higherorder"        @-}
{-@ LIQUID "--exactdc"            @-}

module T1117Lib where

data U1 p = U1

data Product f g p = Product (f p) (g p)
