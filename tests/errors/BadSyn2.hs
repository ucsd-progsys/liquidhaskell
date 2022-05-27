module BadSyn2 where

type Foo = Int

{-@ bob :: Foo 1000 @-}
bob = 10 :: Int

