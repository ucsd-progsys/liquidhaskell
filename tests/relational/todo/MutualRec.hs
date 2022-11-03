module This where

{-@ f, g :: x:Nat -> Nat @-}
f, g :: Int -> Int
f x = if x <= 0 then 0 else 1 + g (x - 1)
g x = if x <= 0 then 0 else 1 + f (x - 1)

{-@ relational f ~ g :: {x:_ -> _ ~ y:_ -> _ 
                     | x == y :=> r1 x == r2 y} @-}
