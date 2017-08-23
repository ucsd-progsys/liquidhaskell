{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs" @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}

module ListFunctors where

bar :: Maybe (a -> a) -> a -> a
{-@ bar :: xy:Maybe (a -> a) -> z: a -> {v: a | v == from_Just xy z} @-}
bar xink z = from_Just xink z


{-@ measure from_Just @-}
from_Just :: Maybe a -> a
from_Just (Just x) = x

{- from_Just :: xs:Maybe a -> {v:a  | v == from_Just xs}@-}
