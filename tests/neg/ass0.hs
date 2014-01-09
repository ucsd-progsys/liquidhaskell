module Ass () where

-- import Language.Haskell.Liquid.Prelude (liquidAssert)

{-@ assert foo :: x:a -> {v: a | (v != x) } @-}
foo x = x 

