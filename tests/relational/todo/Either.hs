module Fixme where

{-@ foo :: {v:Either Bool Bool| isLeft v} @-}
foo :: Either Bool Bool
foo = Left True
