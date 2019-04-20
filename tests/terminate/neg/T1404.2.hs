module Absurd where

{-@ foo :: _ -> {False} @-}
foo :: () -> a
foo x = bar x

{-@ bar :: _ -> {False} @-}
bar :: () -> a
bar x = foo x

{-@ oneIsTwo :: {1 == 2} @-}
oneIsTwo = foo ()
