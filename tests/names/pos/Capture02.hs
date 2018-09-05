-- LH issue #1146 

-- tag: rebind 

{-@ exactly :: x:Int -> { n:Int | n = x } @-}
exactly :: Int -> Int 
exactly x = x 

{-@ incr :: n:Int -> { false } @-}
incr :: Int -> Int
incr n = exactly (n + 1)

