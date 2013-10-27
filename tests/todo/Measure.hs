module Measure where



data Foo a = F a 

{-@ measure foo :: a -> Int @-}

{-@ measure bar :: (Foo a) -> Bool
    bar(F xs) = (foo xs)         @-}
