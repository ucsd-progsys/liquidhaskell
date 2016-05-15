
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
module Append where

import Prelude hiding (map)
import Proves

-- | This does not work, see plan
{- funEq :: m1:a  -> m2:{v:a | v == m1} -> {v: Proof | (\y:a -> m1) == (\y:a -> m2)} @-}
funEq :: a  -> a -> Proof
funEq _ _ = True

{-@ funApp :: m1:a  -> m2:{v:a | v == m1} -> {v: Proof | (\y:a -> m1) (m1) == ((\x:a -> m2)) (m2) } @-}
funApp :: a  -> a -> Proof
funApp _ _ = True

{-@ axiomatize bind @-}
bind :: a -> (a -> b) ->  b
bind x f = f x


-- HERE
{- helper :: m:a -> {v: a |  v == bind m (\x:a -> m)} @-}
helper :: Eq a => a -> a
helper m = bind m h
  where
    h   =  \x -> m
