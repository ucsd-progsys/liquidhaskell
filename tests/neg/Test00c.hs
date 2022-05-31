{-@ LIQUID "--expect-any-error" @-}
module Test00c (ok, inc) where

{-@ ok
      :: Int -> Nat
  @-}
ok :: Int -> Int
ok x = x + 120

{-@ inc :: Int -> Nat @-}
inc :: Int -> Int
inc x = x + 10
