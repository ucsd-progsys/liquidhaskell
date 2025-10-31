{-# LANGUAGE GADTs #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module TupleParse where

import Language.Haskell.Liquid.ProofCombinators

{-@ type Ix typ E = {v:typ | prop v = E} @-}

data Foo where
  {-@ MkFoo :: x:Int -> Ix Foo (x, x) @-}
  MkFoo :: Int -> Foo


{-@ type Alias a B = { v:a | B = B } @-}
{-@ tuples :: Alias (a, b) 1 -> Alias (b, a) 1 @-}
tuples :: (a, b) -> (b, a)
tuples (x, y) = (y, x)

{-@ goldbachsconjecture  :: { (1, 2) /= (2, 1) } @-}
goldbachsconjecture :: Proof
goldbachsconjecture = trivial
