module TypeAlias where

data Foo a b = Foo a b

type Bar = Foo Int

{-@ bar :: Bar {v:Int | v = 2} @-}
bar :: Bar Int
bar = Foo 1 2
