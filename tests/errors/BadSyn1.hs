module Zoo where

type Foo = Int

{-@ type Fooz = {v:Int | 1 < v} @-}

{-@ bob :: Fooz 1000 @-}
bob = 10 :: Int

