-- | test reflection away from the source, using the unfoldings of the interface files

-- Note: this pragma is needed so that the unfoldings end up in the
-- interface files, even with `-O0`
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module ReflExt02B where

myAdd :: Int -> Int -> Int
myAdd a b = a + b + 1