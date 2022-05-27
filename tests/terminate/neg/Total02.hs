-- test recConError
module Total02 where

data Foo = Foo {a :: Int, b :: Int}

foo :: Foo
foo = Foo {a = 1}
