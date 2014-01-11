module Test () where

{-@ stupid :: Int -> Int @-}
stupid :: Int -> Int
stupid x = 0

{-@ myId :: x:a -> {v:a | v = x } @-}
myId x = x 

{-@ assert single :: a -> {v: [a] | len(v) > 0} @-}
single x = [x] 


