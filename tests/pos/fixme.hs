module Fixme where

{-@ inline add @-}
add :: Int -> Int -> Int
add x y = x + y

{-@ measure foo @-}
foo :: D -> Int
foo (D x y) = add x y

data D = D Int Int
