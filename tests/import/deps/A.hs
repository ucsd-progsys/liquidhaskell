module A where

{-@ plus :: x:Int -> y:Int -> {v:Int | v = x + y} @-}
plus :: Int -> Int -> Int
plus x y = x + y

test :: String -> (String, String)
test x = ("test", x)

