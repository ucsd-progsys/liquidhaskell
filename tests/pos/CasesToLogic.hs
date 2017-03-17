{-@ LIQUID "--totality"          @-}
{-@ LIQUID "--exact-data-cons"     @-}
{-@ LIQUID "--higherorder"        @-}

module StringIndexing where

data D = D Int Int 


{-@ reflect mappend @-}
mappend :: D -> D -> D 
{-@ mappend :: x:D -> D -> {v:D | v == x} @-}
mappend x@(D i1 i2) (D i3 i4) = x


