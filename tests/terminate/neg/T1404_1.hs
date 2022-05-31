{-@ LIQUID "--expect-any-error" @-}
module T1404_1 where

{-@ foo :: {False} @-}
foo :: ()
foo = bar

{-@ bar :: {False} @-}
bar :: ()
bar = foo

{-@ oneIsTwo :: {1 == 2} @-}
oneIsTwo :: ()
oneIsTwo = foo
