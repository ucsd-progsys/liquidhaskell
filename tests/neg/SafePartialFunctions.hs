{-@ LIQUID "--totality" @-}
module SafePartialFunctions (gotail, gohead) where

import Prelude hiding (fromJust, tail, head)

fromJust :: Maybe a -> a
fromJust (Just a) = a

tail :: [a] -> [a]
tail (x:xs) = xs

head :: [a] -> a
head (x:xs) = x


-- USERS

gotail xs = case xs of
             [] -> []
             y : ys -> tail ys

gohead :: [[a]] -> [a]
gohead xs = map head xs 
