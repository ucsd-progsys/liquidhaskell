{-# LANGUAGE RankNTypes #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--etabeta"    @-}

module FuseMapLam where

import Prelude hiding (map, foldr)
import Language.Haskell.Liquid.ProofCombinators

-- When we allow the parser to accept : in refinements this wont be needed
{-@ reflect append @-}
append :: a -> [a] -> [a]
append = (:)

{-@ reflect map @-}
map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ e []     = e
foldr f e (x:xs) = f x (foldr f e xs)

{-@ reflect build @-}
build :: forall a. (forall b. (a -> b -> b) -> b -> b) -> [a]
build g = g (:) []

{-@ reflect mapFB @-}
mapFB :: forall elt lst a . (elt -> lst -> lst) -> (a -> elt) -> a -> lst -> lst
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

{-@ rewriteMap :: f:(a1 -> a2) -> xs:[a1] 
               -> { build (\c:func(1, [a2, @(0), @(0)]) -> \n:@(0) -> foldr (mapFB c f) n xs) 
                  = map f xs } @-}
rewriteMap :: (a1 -> a2) -> [a1] -> ()
rewriteMap f []     = trivial
rewriteMap f (x:xs) = trivial ? rewriteMap f xs
