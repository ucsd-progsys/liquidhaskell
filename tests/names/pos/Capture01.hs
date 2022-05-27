module Capture01 where

-- LH issue #1146 

-- tag: rebind 

{-@ type Exactly N = { n:Int | n == N } @-}

{-@ incr :: n:Int -> Exactly { n + 1 } @-}
incr :: Int -> Int
incr n = n + 1

main :: IO ()
main = pure ()
