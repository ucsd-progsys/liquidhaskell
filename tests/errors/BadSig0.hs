{-@ LIQUID "--expect-error-containing=Illegal type specification for `BadSig0.foo`" @-}
module BadSig0 where

{-@ measure prop :: a -> b @-}
{-@ type Prop E = {v:_ | pro v = E} @-}

foo :: Int -> Int 
{-@ foo :: n:Int -> Prop 10 @-}
foo x = x + 1
