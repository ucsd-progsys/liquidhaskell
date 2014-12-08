module AVL where

data Tree = Nil | Tree Int Tree Tree

{-@ measure height @-}
height :: Tree -> Int
height Nil          = 0 :: Int
height (Tree _ l r) = (if height l > height r then 1 + height l else 1 + height r)

