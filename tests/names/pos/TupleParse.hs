{-# LANGUAGE GADTs #-}

module TupleParse where

import Language.Haskell.Liquid.ProofCombinators

{-@ type Ix typ E = {v:typ | prop v = E} @-}

data Foo where
  {-@ MkFoo :: x:Int -> Ix Foo (x, x) @-}
  MkFoo :: Int -> Foo
