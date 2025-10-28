{-# LANGUAGE GADTs #-}
{-@ LIQUID "--expect-error-containing=The constructor StratNoLex.MkFoo of the type StratNoLex.Foo was declared stratified but it has a recursive occurence whose index type StratNoLex.Foo" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
module StratNoLex where

import Language.Haskell.Liquid.ProofCombinators

data N = Z | S N

{-@ stratified Foo @-}
data Foo where
  {-@ Swap :: x:N -> y:N -> Prop (Foo x (S y)) -> Prop (Foo (S x) y) @-}
  Swap :: N -> N -> Foo -> Foo
  {-@ MkFoo :: x:N -> y:N -> (Prop (Foo (S x) y) -> FF) -> Prop (Foo x (S y)) @-}
  MkFoo :: N -> N -> (Foo -> Bool) -> Foo
data FOO = Foo N N

{-@ bad :: x:N -> y:N -> Prop (Foo x y) -> { v:Bool | not v } @-}
bad :: N -> N -> Foo -> Bool
bad x     (S y) (MkFoo _ _ f) = f (Swap x y (MkFoo x y f))
bad (S x) y     (Swap _ _ f)  = bad x (S y) f
bad Z     y     (Swap _ _ f)  = error "unreachable"

{-@ verybad :: Prop (Foo Z (S Z)) @-}
verybad :: Foo
verybad = MkFoo Z Z (\f -> bad (S Z) Z f)

{-@ terrible :: { v:Bool | not v } @-}
terrible :: Bool
terrible = bad Z (S Z) verybad
