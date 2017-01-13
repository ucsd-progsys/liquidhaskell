module ReflectLib0 where

{-@ inline gtThan @-}
gtThan :: Int -> Int -> Bool
gtThan x y = x > y


{-@ predicate GreaterThanA X Y = X > Y @-}
