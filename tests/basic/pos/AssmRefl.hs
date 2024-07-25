-- | test if basic assume reflect is functioning 
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl where

foobar :: Int -> Int -> Int 
foobar n m = n + m

{-@ reflect myfoobar @-}
{-@ myfoobar :: (n: Nat) -> (m: Nat) -> Nat @-}
myfoobar :: Int -> Int -> Int 
myfoobar n m = n + m + 1

{-@ assume reflect foobar as myfoobar @-}

{-@ test :: { foobar 3 4 == 8 } @-} 
test :: ()
test = ()