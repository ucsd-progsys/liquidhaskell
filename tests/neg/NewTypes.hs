newtype Foo a = Bar Int

{-@ newtype Foo a = Bar {x :: Nat} @-}

{-@ fromFoo :: Foo a -> Nat @-}
fromFoo :: Foo a -> Int
fromFoo (Bar n) = n

bar = Bar (-1)
