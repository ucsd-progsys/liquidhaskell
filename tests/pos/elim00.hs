{-@ LIQUID "--short-names"  @-}

module Elim where

data Foo = Foo { xx :: Int, yy :: Int }

data Pair a b = PP a b | Emp

{-@ data Foo = Foo {xx :: Int, yy :: {v:Int | xx < v} }  @-}

foo :: Foo -> Foo
foo (Foo xig yog) = Foo wink cow
  where
    PP wink cow   = PP xig yog
