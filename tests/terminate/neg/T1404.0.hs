module Absurd where

{-@ absurd :: {False} @-}
absurd :: a
absurd = let loop x = loop x in
  loop ()

{-@ oneIsTwo :: {1 == 2} @-}
oneIsTwo :: ()
oneIsTwo = absurd
