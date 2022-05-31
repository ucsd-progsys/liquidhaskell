{-@ LIQUID "--expect-error-containing=Malformed application of type alias `BadSyn2.Foo`" @-}
module BadSyn2 where

type Foo = Int

{-@ bob :: Foo 1000 @-}
bob = 10 :: Int

