module SubRef1 where

foo :: Int -> Int
foo x = x

{-@ relational foo ~ foo :: { x:Int -> {v:Int|v = x} ~ y:Int -> {v:Int|v = y} | true :=> x = r1 x && y = r2 y } @-}

bar :: Int -> Int
bar x = foo x

{-@ relational bar ~ bar :: { x:Int -> Int ~ y:Int -> Int | x = y :=> r1 x = r2 y } @-}
