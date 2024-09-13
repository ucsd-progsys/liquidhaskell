-- | test reflection of private variables of imported modules

-- Note: this pragma is needed so that the unfoldings end up in the
-- interface files, even with `-O0`
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

-- Note that we don't export myAdd here
module ReflExt03B (f) where

{-@ f :: a:Nat -> b:Nat -> Nat @-}
f :: Int -> Int -> Int
f a b = myAdd (a * b) b

-- Force myAdd to end up in the unfoldings
{-# INLINE myAdd #-}
{-@ myAdd :: a:Nat -> b:Nat -> Nat / [b] @-}
myAdd :: Int -> Int -> Int
myAdd a 0 = a
myAdd a n = myAdd a (n - 1) + 1