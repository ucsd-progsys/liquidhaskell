{-@ LIQUID "--expect-error-containing=Malformed application of type alias `BadSyn3.Foo`" @-}
module BadSyn3 where

type Foo = Int

{-@ bob :: Foo String @-}
bob = 10 :: Int

