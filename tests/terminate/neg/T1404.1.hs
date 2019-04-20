module Absurd where

{-@ foo :: {False} @-}
foo :: ()
foo = bar

{-@ bar :: {False} @-}
bar :: ()
bar = foo

{-@ oneIsTwo :: {1 == 2} @-}
oneIsTwo :: ()
oneIsTwo = foo
