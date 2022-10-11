{-@ LIQUID "--expect-any-error" @-}
module NewTypes0 where

newtype Foo a = Bar Int


{-@ newtype Foo a = Bar {x :: Nat} @-}

{-@ fromFoo :: Foo a -> {v:Int | v == 0 } @-}
fromFoo :: Foo a -> Int
fromFoo (Bar n) = n
