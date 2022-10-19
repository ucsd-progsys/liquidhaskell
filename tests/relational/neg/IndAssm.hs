{-@ LIQUID "--expect-any-error" @-}
module IndAssm where

{-@ f :: Nat -> y:Nat -> Nat / [y] @-}
f :: Int -> Int -> Int
f x y = if y <= 0 then x else f (x + 1) (y - 1)

{-@ relational f ~ f :: x1:Int -> y1:Int -> Int ~ x2:Int -> y2:Int -> Int 
                     ~~ x1 <= x2 => y1 <= y2 => r1 x1 y1 <= r2 x2 y2 @-}

{-@ f' :: Nat -> Nat -> Nat @-}
f' :: Int -> Int -> Int
f' y x = if y <= 0 then x else f' (y - 1) (x + 1)

{-@ relational f' ~ f' :: x1:Nat -> y1:Nat -> Nat ~ x2:Nat -> y2:Nat -> Nat
                     ~~ x1 <= x2 => y1 <= y2 => r1 x1 y1 <= r2 x2 y2 @-}

