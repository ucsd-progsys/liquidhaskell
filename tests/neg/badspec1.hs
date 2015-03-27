module Zoo where

type Foo = Int

{-@ type Fooz X = {v:Int | X < v} @-}

{-@ bob :: Foo 1000 @-}
bob = 10 :: Int

