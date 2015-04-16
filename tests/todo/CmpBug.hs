module Fixme where

zipWith :: (Char -> Char -> a) -> b -> b -> [a]
zipWith f = zipWith' ((. w2c) . f . w2c)

zipWith' :: (b -> b -> a) -> c -> c -> [a]
zipWith' = undefined

w2c :: a -> Char
w2c = undefined