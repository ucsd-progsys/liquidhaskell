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

{-@ reflect toNat @-}
toNat :: Int -> Int
{-@ toNat :: Nat -> Nat @-}
toNat n = if n == 0 then 0 else (1 + toNat (n - 1))


{-@ myproof :: a -> { v: Int | incr 5 == 6 } @-}
myproof _ = incr 5
