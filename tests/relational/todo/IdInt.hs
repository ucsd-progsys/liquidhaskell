i :: (Num a) => a -> a
i x = x

j :: Int -> Int
j = i 

q :: Int -> Int
q x = j x

{-@ relational q ~ q :: x1:Int -> _  ~ x2:Int -> _ 
                       ~~ x1 < x2 => r1 x1 < r2 x2 @-}

