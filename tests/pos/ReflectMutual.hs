{-@ LIQUID "--exactdc" @-}

module ReflectMutual where

data Foo = Foo {getFoo :: Int}
{-@ data Foo [fromFoo] = Foo {getFoo :: Nat} @-}

{-@ measure fromFoo @-}
fromFoo :: Foo -> Int 
fromFoo (Foo i) = i 

{-@ reflect foo1 @-}
foo1 :: Foo -> Int 
foo1 (Foo i) | i == 0 = 0 
foo1 (Foo n) = foo2 (Foo (n-1))

{-@ reflect foo2 @-}
foo2 :: Foo -> Int 
foo2 (Foo x) | x <= 1 = x
foo2 (Foo n) = foo1 (Foo (n-1))