module T1012 where

{-@
measure select_Product_1 :: Product f g p -> f p
measure select_Product_2 :: Product f g p -> g p
measure select_Product_1_ :: Product f g p -> (f p)
measure select_Product_2_ :: Product f g p -> (g p)
@-}

data Product f g p = Product (f p) (g p)
