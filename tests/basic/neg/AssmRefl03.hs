-- | Type mismatch
{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl03 where

foobar :: Int -> Bool 
foobar n = n `mod` 2 == 0

{-@ reflect myfoobar @-}
{-@ assume reflect foobar as myfoobar @-}
myfoobar :: Bool -> Bool
myfoobar n = True

{-@ test :: { foobar 5 } @-} 
test :: ()
test = ()