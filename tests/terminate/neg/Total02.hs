{-# OPTIONS_GHC -Wno-missing-fields #-}
{-@ LIQUID "--expect-any-error" @-}
-- test recConError
module Total02 where

data Foo = Foo {a :: Int, b :: Int}

foo :: Foo
foo = Foo {a = 1}
