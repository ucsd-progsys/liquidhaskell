{-@ LIQUID "--expect-any-error" @-}
module Rename where

foo x = let bar = foo in bar x
