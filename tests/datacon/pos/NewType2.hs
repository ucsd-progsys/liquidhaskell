module NewType2 where

{-@ measure someFoo @-}
someFoo :: Foo -> Int
someFoo (Foo x) = x + 1

newtype Foo = Foo { getFoo :: Int }
{-@ newtype Foo = Foo { getFoo :: Nat } @-}

{-@ f :: Foo -> {v:Int | v >= 1} @-}
f :: Foo -> Int
f (Foo x) = someFoo (Foo x)

