module Language.Haskell.Liquid.Prelude where

-------------------------------------------------------------------
--------------------------- Arithmetic ----------------------------
-------------------------------------------------------------------

{-@ assume plus   :: x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x + y}  @-}
{-@ assume minus  :: x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x - y} @-}
{-@ assume times  :: x:Int -> y:Int -> Int                           @-}
{-@ assume eq     :: x:Int -> y:Int -> {v:Bool | ((? v) <=> x = y)}  @-}
{-@ assume neq    :: x:Int -> y:Int -> {v:Bool | ((? v) <=> x != y)} @-}
{-@ assume leq    :: x:Int -> y:Int -> {v:Bool | ((? v) <=> x <= y)} @-}
{-@ assume geq    :: x:Int -> y:Int -> {v:Bool | ((? v) <=> x >= y)} @-}
{-@ assume lt     :: x:Int -> y:Int -> {v:Bool | ((? v) <=> x < y)}  @-}
{-@ assume gt     :: x:Int -> y:Int -> {v:Bool | ((? v) <=> x > y)}  @-}
{-@ assume assert :: x:{v:Bool | (? v)} -> {v: Bool | (? v)}         @-}
{-@ assume crash  :: forall a . x:{v:Bool | (? v)} -> a              @-}

{-# NOINLINE plus #-}
plus :: Int -> Int -> Int
plus x y = x + y

{-# NOINLINE minus #-}
minus :: Int -> Int -> Int
minus x y = x - y

{-# NOINLINE times #-}
times :: Int -> Int -> Int
times x y = x * y

-------------------------------------------------------------------
--------------------------- Comparisons ---------------------------
-------------------------------------------------------------------

{-# NOINLINE eq #-}
eq :: Int -> Int -> Bool
eq x y = x == y

{-# NOINLINE neq #-}
neq :: Int -> Int -> Bool
neq x y = not (x == y)

{-# NOINLINE leq #-}
leq :: Int -> Int -> Bool
leq x y = x <= y

{-# NOINLINE geq #-}
geq :: Int -> Int -> Bool
geq x y = x >= y

{-# NOINLINE lt #-}
lt :: Int -> Int -> Bool
lt x y = x < y

{-# NOINLINE gt #-}
gt :: Int -> Int -> Bool
gt x y = x > y

-------------------------------------------------------------------
------------------------ Specifications ---------------------------
-------------------------------------------------------------------

{-# NOINLINE assert #-}
assert :: Bool -> Bool
assert b = b

{-# NOINLINE crash #-}
crash :: Bool -> a 
crash b = undefined 

{-# NOINLINE force #-}
force x = True 

{-# NOINLINE choose #-}
choose :: Int -> Int
choose x = undefined 
