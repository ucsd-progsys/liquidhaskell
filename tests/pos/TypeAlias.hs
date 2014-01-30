module TypeAlias where

data Foo a b = Foo a b

type Bar = Foo Int


{-@ foo :: String  @-}
foo :: String
foo = "mpla"

{-@ bar :: Bar {v:Int | v = 2} @-}
bar :: Bar Int
bar = Foo 1 2
