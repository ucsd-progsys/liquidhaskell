-- TAG: reflect
-- TAG: measure
{-@ LIQUID "--no-totality"     @-}
{-@ LIQUID "--reflection"      @-}

module ExactFunApp where

bar :: Maybe (a -> a) -> a -> a
{-@ bar :: xy:Maybe (a -> a) -> z: a -> {v: a | v == from_Just xy z} @-}
bar xink z = from_Just xink z

{-@ measure from_Just @-}
from_Just :: Maybe a -> a
from_Just (Just x) = x
