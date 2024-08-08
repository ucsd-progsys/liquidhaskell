-- | test the error message when doing reflection of foreign functions with data selectors
-- | W/O having specified the `exactdc`/`reflection` flag

-- Note: this pragma is needed so that the unfoldings end up in the
-- interface files, even with `-O0`
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

-- Note that we don't export Fruit here
module ReflExt02B (calories) where

calories :: Fruit -> Int
calories Apple = 0
calories (Banana i) = i

data Fruit = Apple | Banana Int
