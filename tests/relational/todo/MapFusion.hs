{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
module MapFusion where

import           Prelude                 hiding ( mapM
                                                , Applicative(..)
                                                , Monad(..)
                                                , length
                                                )

{-@ infix   >>= @-}
{-@ infix   >=> @-}
{-@ infix   :   @-}

{-@ reflect mapM @-}
{-@ mapM :: (Int -> Tick Int) -> xs:[Int] -> Tick {os:[Int] | length os == length xs} @-}
mapM :: (Int -> Tick Int) -> [Int] -> Tick [Int]
mapM f []       = pure []
mapM f (x : xs) = step 1 (liftA2 cons (f x) (mapM f xs))

seqMap :: (Int -> Tick Int) -> (Int -> Tick Int) -> [Int] -> Tick [Int]
seqMap _ _ []       = pure []
seqMap f g (x : xs) = step 2 $ liftA2 cons (g fx) (seqMap f g xs)
  where Tick _ fx = f x

compMap :: (Int -> Tick Int) -> (Int -> Tick Int) -> [Int] -> Tick [Int]
compMap _ _ []       = pure []
compMap f g (x : xs) = step 1 $ liftA2 cons (g fx) (compMap f g xs)
  where Tick _ fx = f x

{-@ relational seqMap ~ compMap :: {f1:(Int -> Tick Int) -> g1:(Int -> Tick Int) -> xs1:[Int] -> {v:Tick [Int]|v = mapM f1 xs1 >>= mapM g1}
                                 ~ f2:(Int -> Tick Int) -> g2:(Int -> Tick Int) -> xs2:[Int] -> {v:Tick [Int]|v = mapM (f2 >=> g2) xs2}
                                | f1 = f2 :=> g1 = g2 :=> xs1 = xs2 :=> 
                                    MapFusion.tcost (r1 f1 g1 xs1) = len xs1 + MapFusion.tcost (r2 f2 g2 xs2) &&
                                      MapFusion.tval (r1 f1 g1 xs1) = MapFusion.tval (r2 f2 g2 xs2)} @-}

mapFusion :: (Int -> Tick Int) -> (Int -> Tick Int) -> [Int] -> ()
{-@ mapFusion :: f:(Int -> Tick Int) -> g:(Int -> Tick Int) -> xs:[Int] 
              -> { (tval (mapM f xs >>= mapM g)  == tval (mapM (f >=> g) xs)) && 
                   (tcost (mapM f xs >>= mapM g) == length xs  + tcost (mapM (f >=> g) xs))
                 }
  @-}
mapFusion f g []       = ()
mapFusion f g (_ : xs) = mapFusion f g xs

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
