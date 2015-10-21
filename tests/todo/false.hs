module Foo where

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--native" @-}

{-@ foo :: {v:a | false} @-}
foo  = foo


nat :: Int
{-@ nat :: Nat @-}
nat = 42
