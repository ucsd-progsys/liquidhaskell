module T595a where

data Tree a = Nil | Tree { key :: a, l::Tree a, r :: Tree a}

{-@ data Tree a = Nil
                | Tree { key :: a
                       , l   :: Tree {v:a | v < key }
                       , r   :: Tree {v:a | key < v }
                       }
  @-}
