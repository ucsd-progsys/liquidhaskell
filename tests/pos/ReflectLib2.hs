{-@ LIQUID "--higherorder" @-}

module ReflectLib2 where

{-@ reflect incr @-}
incr :: Int -> Int
incr x = x + 1

{-@ reflect incr2 @-}
incr2 :: Int -> Int -> Int
incr2 x y = x + y

{-@ reflect plus @-}
plus :: Int -> Int
plus x = apply incr x

{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ myproof :: a -> { v: Int | incr 5 == 6 } @-}
myproof _ = incr 5
