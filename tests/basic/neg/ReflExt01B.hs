-- | test reflection away from the source, when the unfoldings are not available

-- Note: this pragma is needed so that NO unfolding will be available to other
-- module. We want to test what happens then.
{-# OPTIONS_GHC -fomit-interface-pragmas #-}

module ReflExt01B where

{-@ f :: a:Nat -> b:Nat -> Nat @-}
f :: Int -> Int -> Int
f a b = a + b