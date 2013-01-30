module TrueSpec (foo) where

import Language.Haskell.Liquid.Prelude (liquidAssert)

{-@ foo :: Int -> Int @-}
foo :: Int -> Int
foo x = liquidAssert (x > 0) $ x + 1
