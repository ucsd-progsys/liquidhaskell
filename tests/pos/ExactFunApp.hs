{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs" @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module ListFunctors where

bar :: Maybe (a -> a) ->  a ->  a
{-@ bar :: x:Maybe (a -> a) -> z: a
        -> {v: a | v == from_Just x z}
  @-}
bar x z = from_Just x z


{-@ measure from_Just @-}
from_Just :: Maybe a -> a
{-@ from_Just :: xs:Maybe a -> {v:a  | v == from_Just xs}@-}
from_Just (Just x) = x
