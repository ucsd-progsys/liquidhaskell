module BadSyn3 where

type Foo = Int

{-@ bob :: Foo String @-}
bob = 10 :: Int

