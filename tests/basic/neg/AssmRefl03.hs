-- | Type mismatch
{-@ LIQUID "--expect-error-containing=\"AssmRefl03.myfoobar\" and \"AssmRefl03.foobar\" should have the same type. But types GHC.Internal.Types.Bool -> GHC.Internal.Types.Bool and GHC.Internal.Types.Int -> GHC.Internal.Types.Bool do not match." @-}
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