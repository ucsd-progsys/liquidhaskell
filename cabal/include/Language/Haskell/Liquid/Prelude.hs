module Language.Haskell.Liquid.Prelude where

-------------------------------------------------------------------
--------------------------- Arithmetic ----------------------------
-------------------------------------------------------------------

{-# NOINLINE plus #-}
{-# ANN plus "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x + y}" #-}
plus :: Int -> Int -> Int
plus x y = x + y

{-# NOINLINE minus #-}
{-# ANN minus "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x - y}" #-}
minus :: Int -> Int -> Int
minus x y = x - y

{-# NOINLINE times #-}
{-# ANN times "x:Int -> y:Int -> Int" #-}
times :: Int -> Int -> Int
times x y = x * y

-------------------------------------------------------------------
--------------------------- Comparisons ---------------------------
-------------------------------------------------------------------

{-# NOINLINE eq #-}
{-# ANN eq "x:Int -> y:Int -> {v:Bool | ((? v) <=> x = y)}" #-}
eq :: Int -> Int -> Bool
eq x y = x == y

{-# NOINLINE neq #-}
{-# ANN neq "x:Int -> y:Int -> {v:Bool | ((? v) <=> x != y)}" #-}
neq :: Int -> Int -> Bool
neq x y = not (x == y)

{-# NOINLINE leq #-}
{-# ANN leq "x:Int -> y:Int -> {v:Bool | ((? v) <=> x <= y)}" #-}
leq :: Int -> Int -> Bool
leq x y = x <= y

{-# NOINLINE geq #-}
{-# ANN geq "x:Int -> y:Int -> {v:Bool | ((? v) <=> x >= y)}" #-}
geq :: Int -> Int -> Bool
geq x y = x >= y

{-# NOINLINE lt #-}
{-# ANN lt "x:Int -> y:Int -> {v:Bool | ((? v) <=> x < y)}" #-}
lt :: Int -> Int -> Bool
lt x y = x < y

{-# NOINLINE gt #-}
{-# ANN gt "x:Int -> y:Int -> {v:Bool | ((? v) <=> x > y)}" #-}
gt :: Int -> Int -> Bool
gt x y = x > y

-------------------------------------------------------------------
------------------------ Specifications ---------------------------
-------------------------------------------------------------------

{-# NOINLINE assert #-}
{-# ANN assert "x:{v:Bool | (? v)} -> {v: Bool | (? v)}" #-}
assert :: Bool -> Bool
assert b = b

{-# NOINLINE crash #-}
{-# ANN crash "forall a . x:{v:Bool | (? v)} -> a" #-}
crash :: Bool -> a 
crash b = undefined 

{-# NOINLINE force #-}
{-# ANN force "forall a . x:a -> Bool" #-}
force x = True 

{-# NOINLINE choose #-}
{-# ANN choose "x: Int -> Int" #-}
choose :: Int -> Int
choose x = undefined 
