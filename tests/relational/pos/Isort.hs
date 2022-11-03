{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
module Isort where

import           Prelude                 hiding ( Applicative(..)
                                                , Monad(..)
                                                , fmap
                                                , length
                                                )
{-@ infix   >>= @-}
{-@ infix   >=> @-}
{-@ infix   :   @-}

-- {-@ reflect insert @-}
-- {-@ insert :: y:Int -> xs:[Int] -> {v:Tick [Int]| leq y xs :=> Isort.tcost v <= 1} @-}
insert :: Int -> [Int] -> Tick [Int]
insert y []                  = pure [y]
insert y xs@(x : _) | y <= x = step 1 $ pure (y : xs)
insert y (x : xs)            = step 1 $ fmap (cons x) (insert y xs)

-- {-@ reflect isort @-}
isort :: [Int] -> Tick [Int]
isort []       = pure []
isort (x : xs) = step t $ insert x xs' where Tick t xs' = isort xs

-- Unary 

-- {-@ isortThm :: {xs:[Int]|sorted xs} -> {ys:[Int]|len ys = len xs} -> 
--                   {tcost (isort xs) <= tcost (isort ys)} @-}
-- isortThm :: [Int] -> [Int] -> ()
-- isortThm [] [] = ()
-- isortThm (x:xs) (y:ys) = undefined

-- Relational

{-@ relational isort ~ isort :: {xs1:[Int] -> Tick [Int]
                              ~ xs2:[Int] -> Tick [Int]
                             | Isort.sorted xs1 && len xs1 = len xs2 :=> 
                                  Isort.tcost (r1 xs1) <= Isort.tcost (r2 xs2)} @-}

-- Axiomatization

{-@ reflect leq @-}
leq :: Int -> [Int] -> Bool
leq _ []       = True
leq y (x : xs) = y <= x && leq y xs

{-@ reflect sorted @-}
sorted :: [Int] -> Bool
sorted []       = True
sorted (x : xs) = sorted xs && leq x xs

-- Data.Lists

{- HLINT ignore "Use foldr" -}

{-@ measure length @-}
{-@ length :: [a] -> Nat @-}
length :: [a] -> Int
length []       = 0
length (x : xs) = 1 + length xs

{-@ reflect cons @-}
{-@ cons :: x:a -> xs:[a] -> {z:[a] | z == x:xs && length z == length xs + 1} @-}
cons :: a -> [a] -> [a]
cons x xs = x : xs

-- Data.RTrick

data Tick a = Tick { tcost :: Int, tval :: a }
{-@ data Tick a = Tick { tcost :: Int, tval :: a } @-}

{-@ reflect pure @-}
pure :: a -> Tick a
pure x = Tick 0 x

{-@ reflect fmap @-}
fmap :: (a -> b) -> Tick a -> Tick b
fmap f (Tick i x) = Tick i (f x)

{-@ reflect liftA2 @-}
liftA2 :: (a -> b -> c) -> Tick a -> Tick b -> Tick c
liftA2 f (Tick i x) (Tick j y) = Tick (i + j) (f x y)

{-@ reflect >=> @-}
(>=>) :: (a -> Tick b) -> (b -> Tick c) -> a -> Tick c
(>=>) f g x = let Tick i y = f x in let Tick j z = g y in Tick (i + j) z

{-@ reflect >>= @-}
{-@ (>>=) :: mx:Tick a -> m:(a -> Tick b) -> {t:Tick b | tcost t == tcost mx + tcost (m (tval mx)) } @-}
(>>=) :: Tick a -> (a -> Tick b) -> Tick b
Tick i x >>= m = let Tick j w = m x in Tick (i + j) w

{-@ reflect bbind @-}
{-@ bbind :: n:Int -> mx:Tick a -> m:(a -> {t:Tick b | tcost t <= n }) 
          -> {t:Tick b | tcost t <= tcost mx + n } @-}
bbind :: Int -> Tick a -> (a -> Tick b) -> Tick b
bbind _ (Tick i x) m = let Tick j w = m x in Tick (i + j) w

{-@ reflect ebind @-}
{-@ ebind :: n:Int -> mx:Tick a -> m:(a -> {t:Tick b | tcost t == n }) 
          -> {t:Tick b | tcost t == tcost mx + n } @-}
ebind :: Int -> Tick a -> (a -> Tick b) -> Tick b
ebind _ (Tick i x) m = let Tick j w = m x in Tick (i + j) w

{-@ reflect step @-}
step :: Int -> Tick a -> Tick a
step i (Tick j x) = Tick (i + j) x

-- Proof.Combinators

type Proof = ()
data QED   = QED

{-@ assert :: b:{Bool | b } -> {b} @-}
assert :: Bool -> ()
assert _ = ()

{-@ (==.) :: x:a -> { y:a | x == y } -> { v:a | x == v && y == v } @-}
infixl 3 ==.
(==.) :: a -> a -> a
_ ==. x = x
{-# INLINE (==.) #-}

{-@ (***) :: a -> QED -> Proof  @-}
infixl 1 ***
(***) :: a -> QED -> Proof
_ *** _ = ()
{-# INLINE (***) #-}

{-@ (?) :: x:a -> Proof -> { v:a | x == v } @-}
infixl 3 ?
(?) :: a -> Proof -> a
x ? _ = x
{-# INLINE (?) #-}

-- Proof.Quantified

infixl 3 <=>
{-@ (<=>) :: t1:Tick a 
          -> t2:{Tick a | tval t1 == tval t2 && tcost t2 == tcost t1} 
          -> {t:Tick a | t == t2 && tval t1 == tval t && tval t2 == tval t && tcost t == tcost t2 && tcost t2 == tcost t } @-}
(<=>) :: Tick a -> Tick a -> Tick a
(<=>) _ x = x

infixl 3 >==
{-@ (>==) :: t1:Tick a -> i:Int
          -> t2:{Tick a | tval t1 == tval t2 && tcost t1 == i + tcost t2} 
          -> {t:Tick a | t == t2 && tval t1 == tval t && tval t2 == tval t && 
                         tcost t1 == i + tcost t && tcost t == tcost t2 } @-}
(>==) :: Tick a -> Int -> Tick a -> Tick a
(>==) _ _ x = x

infixl 3 ==>
(==>) :: (a -> b) -> a -> b
f ==> x = f x

infixl 3 <==
{-@ (<==) :: t1:Tick a -> i:Int
          -> t2:{Tick a | tval t1 == tval t2 && i + tcost t1 ==  tcost t2} 
          -> {t:Tick a | t == t2 && tval t1 == tval t && tval t2 == tval t && 
                         i + tcost t1 == tcost t && tcost t == tcost t2 } @-}
(<==) :: Tick a -> Int -> Tick a -> Tick a
(<==) _ _ x = x

infixl 3 ==<
(==<) :: (a -> b) -> a -> b
f ==< x = f x
