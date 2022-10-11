{-@ LIQUID "--expect-any-error" @-}
module T1404_0 where

{-@ absurd :: {False} @-}
absurd :: a
absurd = let loop x = loop x in
  loop ()

{-@ oneIsTwo :: {1 == 2} @-}
oneIsTwo :: ()
oneIsTwo = absurd
