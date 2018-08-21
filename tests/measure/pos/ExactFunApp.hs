-- TAG: reflect
-- TAG: measure

{-@ LIQUID "--no-totality"     @-}
{-@ LIQUID "--reflection"      @-}
{-@ LIQUID "--higherorderqs"   @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}

module ListFunctors where

bar :: Maybe (a -> a) -> a -> a
{-@ bar :: xy:Maybe (a -> a) -> z: a -> {v: a | v == from_Just xy z} @-}
bar xink z = from_Just xink z

-- TODO-REBARE: this FAILS with `measure`, but works with `reflect` ?
{-@ measure from_Just @-}
from_Just :: Maybe a -> a
from_Just (Just x) = x

{-@ how :: f:(a -> b -> c) -> x:a -> y:b -> {v: c | v = f x y} @-}
how :: (a -> b -> c) -> a -> b -> c
how  g y z = g y z

