module spec Prelude where

import GHC.Base
import GHC.Int
import GHC.List
import GHC.Num
import GHC.Real
import GHC.Word

import Data.Maybe
import GHC.Exts


GHC.Exts.D# :: x:_ -> {v:_ | v = x}

assume GHC.Base.. :: forall <p :: b -> c -> Prop, q :: a -> b -> Prop, r :: a -> c -> Prop>. 
                     {xcmp::a, wcmp::b<q xcmp> |- c<p wcmp> <: c<r xcmp>}
                     (ycmp:b -> c<p ycmp>)
                  -> (zcmp:a -> b<q zcmp>)
                  ->  xcmp:a -> c<r xcmp>
assume GHC.Integer.smallInteger :: x:GHC.Prim.Int#
                                -> { v:Integer |
                                     v = (x :: int) }
assume GHC.Num.+                :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x + y }
assume GHC.Num.-                :: (GHC.Num.Num a) => x:a -> y:a -> {v:a | v = x - y }

embed GHC.Types.Double as real
embed Integer  as int

type GeInt N = {v: GHC.Types.Int | v >= N }
type LeInt N = {v: GHC.Types.Int | v <= N }
type Nat     = {v: GHC.Types.Int | v >= 0 }
type Even    = {v: GHC.Types.Int | (v mod 2) = 0 }
type Odd     = {v: GHC.Types.Int | (v mod 2) = 1 }
type BNat N  = {v: Nat           | v <= N }    
type TT      = {v: Bool          | Prop v}
type FF      = {v: Bool          | not (Prop v)}

predicate Max V X Y = if X > Y then V = X else V = Y
predicate Min V X Y = if X < Y then V = X else V = Y

type IncrListD a D = [a]<{\x y -> (x+D) <= y}>
