module ReflectLib0 where

{-@ inline greaterThan @-}
greaterThan :: Int -> Int -> Bool
greaterThan x y = x > y


{-@ predicate GreaterThanA X Y = X > Y @-}
