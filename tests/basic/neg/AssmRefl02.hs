-- | Duplicate reflection
{-@ LIQUID "--expect-error-containing=Duplicate reflection of \"foobar\"" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl02 where

{-@ reflect foobar @-}
foobar :: Int -> Bool 
foobar n = n `mod` 2 == 0

{-@ reflect myfoobar @-}
{-@ assume reflect foobar as myfoobar @-}
myfoobar :: Int -> Bool
myfoobar n = n `mod` 2 == 1

{-@ test :: { foobar 5 } @-} 
test :: ()
test = ()
