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

{-@ assume liquidAssertB :: x:{v:Bool | (? v)} -> {v: Bool | (? v)} @-}
{-# NOINLINE liquidAssertB #-}
liquidAssertB :: Bool -> Bool
liquidAssertB b = b

{-@ assume liquidAssert :: {v:Bool | (? v)} -> a -> a  @-}
{-# NOINLINE liquidAssert #-}
liquidAssert :: Bool -> a -> a 
liquidAssert b x = x

{-@ assume liquidAssume :: b:Bool -> a -> {v: a | (? b)}  @-}
{-# NOINLINE liquidAssume #-}
liquidAssume :: Bool -> a -> a 
liquidAssume b x = x



{-@ assume liquidError :: {v: String | 0 = 1} -> a  @-}
{-# NOINLINE liquidError #-}
liquidError :: String -> a
liquidError = error 

{-@ assume crash  :: forall a . x:{v:Bool | (? v)} -> a              @-}
{-# NOINLINE crash #-}
crash :: Bool -> a 
crash b = undefined 

{-# NOINLINE force #-}
force x = True 

{-# NOINLINE choose #-}
choose :: Int -> Int
choose x = undefined 

-------------------------------------------------------------------
----------- Modular Arithmetic Wrappers ---------------------------
-------------------------------------------------------------------

-- tedium because fixpoint doesnt want to deal with (x mod y) only (x mod c)
{-@ assume isEven :: x:Int -> {v:Bool | ((? v) <=> ((x mod 2) = 0))} @-}
{-# NOINLINE isEven #-}
isEven   :: Int -> Bool
isEven x = x `mod` 2 == 0

{-@ assume isOdd :: x:Int -> {v:Bool | ((? v) <=> ((x mod 2) = 1))} @-}
{-# NOINLINE isOdd #-}
isOdd   :: Int -> Bool
isOdd x = x `mod` 2 == 1


