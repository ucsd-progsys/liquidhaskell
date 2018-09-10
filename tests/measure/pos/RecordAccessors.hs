module RecordAccessors where

{-@ type Big = {v:Int | v > 666} @-}


{-@ data Foo = F { thing :: Big } @-}
data Foo = F { thing :: Int }

{-@ bar :: Foo -> Big @-}
bar = thing

{-@ baz :: Foo -> Big @-}
baz (F n) = n
