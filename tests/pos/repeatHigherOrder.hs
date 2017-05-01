{-@ LIQUID "--no-termination" @-}

module Repeat where

import Prelude hiding (repeat, succ)
import Language.Haskell.Liquid.Prelude

repeat :: Int -> (a -> a) -> a -> a
goal   :: Int -> Int
     
{-@ bound step @-}
step :: (a -> a -> Bool) -> (Int -> a -> Bool) -> Int -> a -> a -> Bool
step pf pr = \ i x x' -> pr (i - 1) x ==> pf x x' ==> pr i x'

-- This syntax is not yet supported in liquidhaskell-8
{- repeat :: forall a <f :: a -> a -> Bool, r :: Int -> a -> Bool>.
                (Step a f r) => 
                 n:Nat -> (y:a -> a<f y>) -> a<r 0> -> a<r n>
  @-}


{-@ repeat :: forall a <f :: a -> a -> Bool, r :: Int -> a -> Bool>.
                {i::Int, x::a<r (i-1)>|- a<f x> <:a <r i>}
                 n:Nat -> (y:a -> a<f y>) -> a<r 0> -> a<r n>
  @-}
repeat 0 _ x = x
repeat n f x = repeat (n - 1) f (f x)

{-@ goal :: n:Nat -> {r:Nat | n <= r} @-}
goal n = repeat n (+ 1) 0

