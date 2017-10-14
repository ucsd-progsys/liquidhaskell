{-@ LIQUID "--exact-data-cons"     @-}
{-@ LIQUID "--higherorder"        @-}

module StringIndexing where

-- ISSUE: Uncomment the below to make this test pass
--
--    import Prelude hiding (mappend)
-- 
-- LH should give an error message indicating the above.

data D = D Int Int 

{-@ reflect mappend @-}
mappend :: D -> D -> D 

{-@ mappend :: x:D -> D -> {v:D | v == x} @-}
mappend x@(D i1 i2) (D i3 i4) = x

