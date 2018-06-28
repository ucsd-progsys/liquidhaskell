{-@ reflect f @-}
{-@ f :: Nat -> Nat @-}
f :: Int -> Int
f i | i == 0 = 1
f x = x * (f (x-1))

{-@ f' :: x :{ Nat | true} -> { y : Nat | x <= y} -> (fx :: Int, {fy:Int | fx <= fy }) @-}
f' :: Int -> Int -> (Int, Int)
f' x y = (f x, f y)