
{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

module Append where

import Proves

import Prelude hiding (map)


{-@ lamEq :: a -> {v: Proof | (\y:a -> y) == (\x:a -> x)} @-}
lamEq :: a -> Proof
lamEq _ = simpleProof

{-@ funEq :: m1:a  -> m2:{v:a | v == m1} -> {v: Proof | (\y:a -> m1) == (\y:a -> m2)} @-}
funEq :: a  -> a -> Proof
funEq _ _ = simpleProof


{-@ funIdEq :: m1:a  -> m2:{v:a | v == m1} -> {v: Proof | (\x:a -> (\y:a -> y)) == (\z:a -> (\x:a -> x))} @-}
funIdEq :: a  -> a -> Proof
funIdEq _ _ = simpleProof

{-@ funApp :: m1:a  -> m2:{v:a | v == m1} -> {v: Proof | (\y:a -> m1) (m1) == ((\x:a -> m2)) (m2) } @-}
funApp :: a  -> a -> Proof
funApp _ _ = simpleProof



{-@ axiomatize bind @-}
bind :: a -> (a -> b) ->  b
bind x f = f x

{-@ helper :: m:a -> {v: a |  v == bind m (\x:a -> m)} @-}
helper :: a -> a
helper m = bind m h
  where
    h   =  \x -> m
