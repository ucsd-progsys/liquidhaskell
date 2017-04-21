{-# LANGUAGE MagicHash      #-}

module Language.Haskell.Liquid.Prelude where

-------------------------------------------------------------------
--------------------------- Arithmetic ----------------------------
-------------------------------------------------------------------

{-@ assume plus   :: x:{v:GHC.Types.Int | true } -> y:{v:GHC.Types.Int | true} -> {v:GHC.Types.Int | v = x + y}  @-}
{-@ assume minus  :: x:{v:GHC.Types.Int | true } -> y:{v:GHC.Types.Int | true} -> {v:GHC.Types.Int | v = x - y} @-}
{-@ assume times  :: x:GHC.Types.Int -> y:GHC.Types.Int -> GHC.Types.Int                           @-}
{-@ assume eq     :: x:GHC.Types.Int -> y:GHC.Types.Int -> {v:GHC.Types.Bool | ((v) <=> x = y)}  @-}
{-@ assume neq    :: x:GHC.Types.Int -> y:GHC.Types.Int -> {v:GHC.Types.Bool | ((v) <=> x != y)} @-}
{-@ assume leq    :: x:GHC.Types.Int -> y:GHC.Types.Int -> {v:GHC.Types.Bool | ((v) <=> x <= y)} @-}
{-@ assume geq    :: x:GHC.Types.Int -> y:GHC.Types.Int -> {v:GHC.Types.Bool | ((v) <=> x >= y)} @-}
{-@ assume lt     :: x:GHC.Types.Int -> y:GHC.Types.Int -> {v:GHC.Types.Bool | ((v) <=> x < y)}  @-}
{-@ assume gt     :: x:GHC.Types.Int -> y:GHC.Types.Int -> {v:GHC.Types.Bool | ((v) <=> x > y)}  @-}

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


{-@ assume liquidAssertB :: x:{v:GHC.Types.Bool | v} -> {v: GHC.Types.Bool | v} @-}
{-# NOINLINE liquidAssertB #-}
liquidAssertB :: Bool -> Bool
liquidAssertB b = b

{-@ assume liquidAssert :: {v:GHC.Types.Bool | v} -> a -> a  @-}
{-# NOINLINE liquidAssert #-}
liquidAssert :: Bool -> a -> a
liquidAssert _ x = x

{-@ assume liquidAssume :: b:GHC.Types.Bool -> a -> {v: a | b}  @-}
{-# NOINLINE liquidAssume #-}
liquidAssume :: Bool -> a -> a
liquidAssume b x = if b then x else error "liquidAssume fails"

{-@ assume liquidAssumeB :: forall <p :: a -> Bool>. (a<p> -> {v:GHC.Types.Bool| v}) -> a -> a<p> @-}
liquidAssumeB :: (a -> Bool) -> a -> a
liquidAssumeB p x | p x = x
                  | otherwise = error "liquidAssumeB fails"



{-@ assume liquidError :: {v:GHC.Base.String | 0 = 1} -> a  @-}
{-# NOINLINE liquidError #-}
liquidError :: String -> a
liquidError = error

{-@ assume crash  :: forall a . x:{v:GHC.Types.Bool | v} -> a @-}
{-# NOINLINE crash #-}
crash :: Bool -> a
crash = undefined

{-# NOINLINE force #-}
force :: Bool
force = True

{-# NOINLINE choose #-}
choose :: Int -> Int
choose = undefined

-------------------------------------------------------------------
----------- Modular Arithmetic Wrappers ---------------------------
-------------------------------------------------------------------

-- tedium because fixpoint doesnt want to deal with (x mod y) only (x mod c)
{-@ assume isEven :: x:GHC.Types.Int -> {v:GHC.Types.Bool | ((v) <=> ((x mod 2) = 0))} @-}
{-# NOINLINE isEven #-}
isEven   :: Int -> Bool
isEven x = x `mod` 2 == 0

{-@ assume isOdd :: x:GHC.Types.Int -> {v:GHC.Types.Bool | ((v) <=> ((x mod 2) = 1))} @-}
{-# NOINLINE isOdd #-}
isOdd   :: Int -> Bool
isOdd x = x `mod` 2 == 1

-----------------------------------------------------------------------------------------------

{-@ assert safeZipWith :: (a -> b -> c) -> xs : [a] -> ys:{v:[b] | len(v) = len(xs)} -> {v : [c] | len(v) = len(xs)} @-}
safeZipWith :: (a->b->c) -> [a]->[b]->[c]
safeZipWith f (a:as) (b:bs) = f a b : safeZipWith f as bs
safeZipWith _ []     []     = []
safeZipWith _ _ _ = error "safeZipWith: cannot happen!"




{-@ (==>) :: p:GHC.Types.Bool -> q:GHC.Types.Bool -> {v:GHC.Types.Bool | v <=> (p =>  q)} @-}
infixr 8 ==>
(==>) :: Bool -> Bool -> Bool
False ==> False = True
False ==> True  = True
True  ==> True  = True
True  ==> False = False
