module ListSort () where

data Foo a = F Int a

{-@ data Foo a = F {tag :: Int, f :: a} @-}

foo = F
