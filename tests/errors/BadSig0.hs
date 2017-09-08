module Zoo where

{-@ measure prop :: a -> b @-}
{-@ type Prop E = {v:_ | pro v = E} @-}

foo :: Int -> Int 
{-@ foo :: n:Int -> Prop 10 @-}
foo x = x + 1
