module spec Prelude where

import GHC.Base
import GHC.Int
import GHC.List
import GHC.Num
import GHC.Real
import GHC.Word

import Data.Maybe

assume GHC.Base..               :: forall< p :: xx:b -> c -> Prop
                                         , q :: yy:a -> b -> Prop>.
                                      f:(x:b -> c<p x>) ->
                                      g:(y:a -> b<q y>) ->
                                      x:a ->
                                      exists[z:b<q x>].c<p z>
assume GHC.Integer.smallInteger :: x:GHC.Prim.Int#
                                -> { v:GHC.Integer.Type.Integer |
                                     v = (x :: int) }
assume GHC.Num.+                :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x + y }
assume GHC.Num.-                :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x - y }
assume GHC.Num.*                :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x * y}

embed GHC.Integer.Type.Integer  as int

type GeInt N = {v: GHC.Types.Int | v >= N }
type LeInt N = {v: GHC.Types.Int | v <= N }
type Nat     = {v: GHC.Types.Int | v >= 0 }
type Even    = {v: GHC.Types.Int | (v mod 2) = 0 }
type Odd     = {v: GHC.Types.Int | (v mod 2) = 1 }
type BNat N  = {v: Nat           | v <= N }    

predicate Max V X Y = ((X > Y) ? (V = X) : (V = Y))
predicate Min V X Y = ((X < Y) ? (V = X) : (V = Y))

type IncrListD a D = [a]<{\x y -> (x+D) <= y}>
