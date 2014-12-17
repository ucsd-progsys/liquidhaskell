module Measures where

import Data.Set 

{-@ LIQUID "--no-termination" @-}
{-@ measure elements @-}
{-@ measure dups @-}

data F a = F a |  C a (F a) | E 

dups :: Ord a => F a -> Set a
dups E        = empty
dups (F a)    = empty
dups (C x xs) = if member x (elements xs) then singleton x `union` dups xs else dups xs

elements :: Ord a => F a -> Set a
elements E        = empty
elements (F a)    = singleton a
elements (C x xs) = singleton x `union` elements xs



{-@ foo :: (Ord a) => x:F a -> {v:Set a | (dups x) = v} @-}
foo :: Ord a => F a -> Set a
foo E        = empty
foo (F a)    = empty
foo (C x xs) = if member x (elements xs) then singleton x `union` foo xs else foo xs
