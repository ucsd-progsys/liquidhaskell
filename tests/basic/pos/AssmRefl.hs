-- | test if basic assume reflect Lis functioning 
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Inc00 where

{-@ measure GHC.Num.fromInteger :: Integer -> a @-}

foobar :: Int -> Bool 
foobar n = n `mod` 2 == 0

{-@ assume reflect myfoobar as foobar @-}
myfoobar :: Bool -> Bool 
myfoobar _ = 5 `mod` 2 == 0

{-@ test :: { not (foobar 5) } @-} 
test :: ()
test = ()