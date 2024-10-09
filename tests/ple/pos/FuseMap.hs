{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--etabeta"    @-}

module FuseMap where

import Prelude hiding (map, foldr)
import Language.Haskell.Liquid.ProofCombinators

-- When we allow the parser to accept lambdas in reflected
-- functions this wont be needed
{-@reflect append @-}
append = (:)

{-@ reflect map @-}
map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ e []     = e
foldr f e (x:xs) = f x (foldr f e xs)

{-@ reflect mapFB @-}
mapFB ::  (elt -> lst -> lst) -> (a -> elt) -> a -> lst -> lst
mapFB c f = \x ys -> c (f x) ys

{-@ rewriteMapList :: f:_ -> b:_ -> { foldr (mapFB append f) [] b = map f b } @-}
rewriteMapList :: (a -> b) -> [a] -> ()
rewriteMapList f []     = trivial
rewriteMapList f (x:xs) = trivial ? (rewriteMapList f xs)

{-@ rewriteMapFB :: c:_ -> f:_ -> g:_ -> { mapFB (mapFB c f) g = mapFB c (f . g) } @-}
rewriteMapFB :: (a -> b -> b) -> (c -> a) -> (d -> c) -> Proof
rewriteMapFB c f g = trivial

{-@ rewriteMapFBid :: c:(a -> b -> b) -> { mapFB c (\x:a -> x) = c } @-}
rewriteMapFBid :: (a -> b -> b) -> ()
rewriteMapFBid c = trivial