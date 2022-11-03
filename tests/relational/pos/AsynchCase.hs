module AsynchCase where


{-@ assume relational foo ~ foo :: { x1:Int -> Int ~ x2:Int -> Int | x1 < x2 :=> r1 x1 < r2 x2 } @-}
foo :: Int -> Int
foo = undefined

{-@ relational bar ~ bar :: { a1:Bool -> b1:Bool -> Int ~ a2:Bool -> b2:Bool -> Int 
                         | a1 && not a2 :=> true :=> r1 a1 b1 < r2 a2 b2 } @-}
bar :: Bool -> Bool -> Int
bar True  _ = foo 1
bar False x = if x then foo 2 else foo 3
