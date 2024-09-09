-- | Assume reflect import test
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl02A where

foobar :: Int -> Bool
foobar n = n `mod` 2 <= 4