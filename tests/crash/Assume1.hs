a :: Int
a = 0

{-@ assume b :: { b : Int | a < b } @-}
b :: Int
b = 1

{-@
f :: a : Int -> { b : Int | a < b } -> ()
@-}
f :: Int -> Int -> ()
f _ _ = ()

g :: ()
g = f a b