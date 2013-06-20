module spec Prelude where

import GHC.Base
import GHC.List

-- assume GHC.Base..               :: forall< p :: xx:b -> c -> Prop
--                                          , q :: yy:a -> b -> Prop>.
--                                       f:(x:b -> c<p x>) ->
--                                       g:(y:a -> b<q y>) ->
--                                       x:a ->
--                                       exists[z:b<q x>].c<p z>
assume GHC.Integer.smallInteger :: x:GHC.Prim.Int# -> {v:GHC.Integer.Type.Integer | v = (x :: GHC.Integer.Type.Integer)}
assume GHC.Num.+                :: (Num a) => x:a -> y:a -> {v:a | v = x + y }
assume GHC.Num.-                :: (Num a) => x:a -> y:a -> {v:a | v = x - y }
assume GHC.Num.*                :: (Num a) => x:a -> y:a -> {v:a | ((((x >= 0) && (y >= 0)) => ((v >= x) && (v >= y))) && (((x > 1) && (y > 1)) => ((v > x) && (v > y)))) }
assume GHC.Real.div             :: (Integral a) => x:a -> y:a -> {v:a | v = (x / y) }
-- fixpoint can't handle (x mod y), only (x mod c) so we need to be more clever here
-- assume GHC.Real.mod             :: (Integral a) => x:a -> y:a -> {v:a | v = (x mod y) }
assume GHC.Real./               :: (Fractional a) => x:a -> y:{v:a | v != 0} -> {v: a | v = (x / y) }

assume GHC.Num.fromInteger      :: (Num a) => x:Integer -> {v:a | v = x }
assume GHC.Real.toInteger       :: (Integral a) => x:a -> {v:Integer | v = x}
assume GHC.Real.fromIntegral    :: (Integral a, Num b) => x:a -> {v:b|v=x}



measure isJust :: forall a. Maybe a -> Prop
isJust (Just x)  = true
isJust (Nothing) = false

measure fromJust :: forall a. Maybe a -> a
fromJust (Just x) = x

embed GHC.Integer.Type.Integer  as int

type GeInt N = {v: GHC.Types.Int | v >= N }
type LeInt N = {v: GHC.Types.Int | v <= N }
type Nat     = {v: GHC.Types.Int | v >= 0 }
type BNat N  = {v: Nat           | v <= N }    

predicate Max V X Y = ((X > Y) ? (V = X) : (V = Y))
predicate Min V X Y = ((X < Y) ? (V = X) : (V = Y))

predicate Btwn V X Y   = ((X <= V) && (V < Y))
predicate BtwnE V X Y  = ((X < V)  && (V < Y))
predicate BtwnI V X Y  = ((X <= V) && (V <= Y))
predicate BtwnEI V X Y = ((X < V)  && (V <= Y))

