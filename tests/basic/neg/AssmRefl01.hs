-- | Testing when the pretended function is not reflected into the logic
{-@ LIQUID "--expect-error-containing=myfoobar must be reflected first using {-@ reflect myfoobar @-}" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl01 where

foobar :: Int -> Bool 
foobar n = n `mod` 2 == 0

{-@ assume reflect foobar as myfoobar @-}
myfoobar :: Int -> Bool
myfoobar n = n `mod` 2 == 1

{-@ test :: { foobar 5 } @-} 
test :: ()
test = ()
