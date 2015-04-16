module Fixme where

{-
Interesting example as subtyping of bounds is instantiated
with function types!
-}

zipWith :: (b -> Char -> a) 
        -> b -> b -> a
zipWith f =  (bar . f)

bar :: (Char -> c) -> a -> c
bar = undefined

