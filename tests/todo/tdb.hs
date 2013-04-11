module Main where

zero' :: Int
zero' = 0
{-@ zero' :: {v: Int | false } @-}

-- Throws NASTY GHC error because "Int" is not a tycon * -> *
-- Should be some nicer error message that we can produce...
{-@ print' :: Int {v: Int | true } -> IO () @-}
print' :: Int -> IO ()
print' = print

main = print' zero'
