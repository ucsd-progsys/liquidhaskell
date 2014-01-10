module SafePartialFunctions (gotail, gohead) where

{-@ LIQUID "--totality" @-}
import Prelude hiding (fromJust, tail, head)

{-@ fromJust :: {v:Maybe a | (isJust v)} -> a @-}
fromJust :: Maybe a -> a
fromJust (Just a) = a

{-@ tail :: {v:[a] | ((len v) > 0)}-> [a] @-}
tail :: [a] -> [a]
tail (x:xs) = xs

{-@ head :: {v:[a] | ((len v) > 0)}-> a @-}
head :: [a] -> a
head (x:xs) = x


-- USERS

gotail xs = case xs of
             [] -> []
             y : ys -> tail xs

{-@ gohead :: [{v:[a] | ((len v) > 0)}] -> [a] @-}
gohead :: [[a]] -> [a]
gohead xs = map head xs 
