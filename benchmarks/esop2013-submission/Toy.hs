{-@ LIQUID "--pruneunsorted" @-}

{-@ LIQUID "--no-termination" @-}

module Toy () where

import Language.Haskell.Liquid.Prelude (isEven)

-------------------------------------------------------------------------
-- | Parametric Invariants over Base Types ------------------------------
-------------------------------------------------------------------------

maxInt     :: Int -> Int -> Int 
maxInt x y = if x <= y then y else x 

maximumInt ::  [Int] -> Int 
maximumInt (x:xs) = foldr maxInt x xs

{-@ maxEvens1 :: [Int] -> {v:Int | v mod 2 = 0 } @-}
maxEvens1 xs = maximumInt (0 : xs') 
  where xs' = [ x | x <- xs, isEven x]

-------------------------------------------------------------------------
-- | Parametric Invariants over Class-Predicated Tyvars -----------------
-------------------------------------------------------------------------

maxPoly     :: (Ord a) => a -> a -> a 
maxPoly x y = if x <= y then y else x

maximumPoly :: (Ord a) => [a] -> a
maximumPoly (x:xs) = foldr maxPoly x xs

{-@ maxEvens2 :: [Int] -> {v:Int | v mod 2 = 0 } @-}
maxEvens2 xs = maximumPoly (0 : xs') 
  where xs' = [ x | x <- xs, isEven x]

-------------------------------------------------------------------------
-- | Induction over Int Ranges ------------------------------------------
-------------------------------------------------------------------------

{-@ foldN :: forall a <p :: x0:Int -> x1:a -> Prop>. 
                (i:Int -> a<p i> -> a<p (i+1)>) 
              -> n:{v: Int | v >= 0}
              -> a <p 0> 
              -> a <p n>
  @-}

foldN :: (Int -> a -> a) -> Int -> a -> a
foldN f n = go 0 
  where go i x | i < n     = go (i+1) (f i x)
               | otherwise = x

{-@ count :: m: {v: Int | v > 0 } -> {v: Int | v = m} @-}
count :: Int -> Int
count m = foldN (\_ n -> n + 1) m 0

-------------------------------------------------------------------------
-- | Induction over Data types ------------------------------------------
-------------------------------------------------------------------------

data Vec a = Nil | Cons a (Vec a)

{-@ data Vec [llen] a = Nil | Cons (x::a) (xs::Vec a) @-}

-- | We can encode the notion of length as an inductive measure @llen@ 

{-@ measure llen     :: forall a. Vec a -> Int 
    llen (Nil)       = 0 
    llen (Cons x xs) = 1 + llen(xs)
  @-}

-- | As a warmup, lets check that a /real/ length function indeed computes
-- the length of the list.

{-@ sizeOf :: xs:Vec a -> {v: Int | v = llen(xs)} @-}
sizeOf             :: Vec a -> Int
sizeOf Nil         = 0
sizeOf (Cons _ xs) = 1 + sizeOf xs

-------------------------------------------------------------------------
-- | Higher-order fold -------------------------------------------------- 
-------------------------------------------------------------------------

-- | Time to roll up the sleeves. Here's a a higher-order @foldr@ function
-- for our `Vec` type. Note that the `op` argument takes an extra /ghost/
-- parameter that will let us properly describe the type of `efoldr` 

{-@ efoldr :: forall a b <p :: x0:Vec a -> x1:b -> Prop>. 
                (xs:Vec a -> x:a -> b <p xs> -> b <p (Toy.Cons x xs)>) 
              -> b <p Toy.Nil> 
              -> ys: Vec a
              -> b <p ys>
  @-}
efoldr :: (Vec a -> a -> b -> b) -> b -> Vec a -> b
efoldr op b Nil         = b
efoldr op b (Cons x xs) = op xs x (efoldr op b xs) 

-------------------------------------------------------------------------
-- | Clients of `efold` ------------------------------------------------- 
-------------------------------------------------------------------------

-- | Finally, lets write a few /client/ functions that use `efoldr` to 
-- operate on the `Vec`s. 

-- | First: Computing the length using `efoldr`
{-@ size :: xs:Vec a -> {v: Int | v = llen(xs)} @-}
size :: Vec a -> Int
size = efoldr (\_ _ n -> n + 1) 0

-- | The above uses a helper that counts up the size. (Pesky hack to avoid writing qualifier v = ~A + 1)
{-@ suc :: x:Int -> {v: Int | v = x + 1} @-}
suc :: Int -> Int
suc x = x + 1 

-- | Second: Appending two lists using `efoldr`
{-@ app  :: xs: Vec a -> ys: Vec a -> {v: Vec a | llen(v) = llen(xs) + llen(ys) } @-} 
app xs ys = efoldr (\_ z zs -> Cons z zs) ys xs 

