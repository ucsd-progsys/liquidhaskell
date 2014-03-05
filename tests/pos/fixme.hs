module Blank where

-- This is a blank file.

data P = P Int

{-@ measure moo :: P -> Prop @-}
{-@ measure poo :: P -> Prop @-}

{-@ alice :: Int -> {v:P | (poo v)} @-}
alice :: Int -> P
alice x = bob x      -- FAILS
-- alice = bob          -- FAILS
-- alice x = let zoo = bob x in zoo

{-@ bob :: Int -> {v:P | (moo v)} @-}
bob :: Int -> P
bob = undefined

{-@ invariant {v:P | ((moo v) => (poo v))} @-}