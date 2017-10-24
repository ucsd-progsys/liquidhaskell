{-@ LIQUID "--exact-data-con" @-}

module T1102_LibZ where

{-@ data Foo a b = Foo { fooA :: a, fooB :: b} @-}
data Foo a b = Foo {fooA :: a, fooB :: b}
