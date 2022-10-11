{-@ LIQUID "--expect-error-containing=Malformed application of type alias `Fooz`" @-}
module BadSyn1 where

type Foo = Int

{-@ type Fooz = {v:Int | 1 < v} @-}

{-@ bob :: Fooz 1000 @-}
bob = 10 :: Int

