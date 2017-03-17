newtype Foo a = Bar Int  


{-@ newtype Foo = Bar {x :: Nat} @-}

{-@ fromFoo :: Foo a -> {v:Int | v == 0 } @-}
fromFoo :: Foo a -> Int 
fromFoo (Bar n) = n 
