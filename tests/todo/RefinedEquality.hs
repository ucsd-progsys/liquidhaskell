{-@ LIQUID "--reflection" @-} 
{-@ LIQUID "--no-adt"     @-} 
{-@ LIQUID "--ple"        @-} 
{-@ LIQUID "--typeclass"  @-} 

{-# LANGUAGE GADTs           #-}
{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module RefinedEquality
--   ( EqT(..), BEq(..)
-- --   , eqRTCtx
-- --   , eqFun
--   , deqFun
--   , eqSMT
--   ) where 
  where 

import Language.Haskell.Liquid.ProofCombinators 

{-@ measure eqT :: a -> a -> Bool @-}
{-@ type EqRT a E1 E2 = {v:EqT a | eqT E1 E2} @-}
-- 
-- 
-- {-@ _eqRTCtx :: x:a -> y:a -> EqRT a {x} {y} -> ctx:(a -> b) -> EqRT b {ctx x} {ctx y}  @-}
-- _eqRTCtx ::  a -> a -> EqT a -> (a -> b) -> EqT b
-- _eqRTCtx = EqCtx  
-- 
-- 
-- {-@ ignore deqFun @-}
-- {-@ deqFun :: forall<p :: a -> b -> Bool>. f:(a -> b) -> g:(a -> b) 
--           -> (x:a -> EqRT b<p x> {f x} {g x}) -> EqRT (y:a -> b<p y>) {f} {g}  @-}
-- deqFun :: (a -> b) -> (a -> b) -> (a -> EqT b) -> EqT (a -> b)
-- deqFun = EqFun
-- 
-- {-@ _eqFun :: f:(a -> b) -> g:(a -> b) 
--           -> (x:a -> EqRT b {f x} {g x}) -> EqRT (a -> b) {f} {g}  @-}
-- _eqFun :: (a -> b) -> (a -> b) -> (a -> EqT b) -> EqT (a -> b)
-- _eqFun = EqFun
-- 
-- {-@ ignore eqSMT @-}
-- {-@ assume eqSMT :: forall <p :: a -> Bool>. BEq a => x:a<p> -> y:a<p> -> {v:() | bEq x y} -> EqRT (a<p>) {x} {y} @-}
-- eqSMT :: BEq a => a -> a -> () -> EqT a
-- eqSMT x y p = EqSMT x y p 
-- 
-- 
data EqT  :: * -> *  where 
   EqSMT  :: BEq a => a -> a -> () -> EqT a 
   EqFun  :: (a -> b) -> (a -> b) -> (a -> EqT b) -> EqT (a -> b)
   EqCtx  :: a -> a -> EqT a -> (a -> b) -> EqT b 


{-@ data EqT  :: * -> *  where 
        EqSMT  :: BEq a => x:a -> y:a -> {v:() | bEq x y} -> EqRT a {x} {y}
     |  EqFun  :: ff:(a -> b) -> gg:(a -> b) -> (x:a -> EqRT b {ff x} {gg x}) -> EqRT (a -> b) {ff} {gg}
     |  EqCtx  :: x:a -> y:a -> EqRT a {x} {y} -> ctx:(a -> b) -> EqRT b {ctx x} {ctx y} 
@-}   

-- class BEq a 
class BEq a where 
  {-@ bEq    :: x:a -> y:a -> Bool @-}
  bEq    :: a -> a -> Bool 
  {-@ reflP  :: x:a -> {bEq x x} @-}
  reflP  :: a -> ()
  symmP  :: a -> a -> ()
  {-@ symmP  :: x:a -> y:a -> { bEq x y => bEq y x } @-}
  transP :: a -> a -> a -> ()
  {-@ transP :: x:a -> y:a -> z:a -> { ( bEq x y && bEq y z) => bEq x z } @-}



-- instance BEq Integer where 
--   bEq = bEqInteger
--   reflP x = const () (bEqInteger x x)     
--   symmP x y  = () `const` (bEqInteger x y)   
--   transP x y z = () `const` (bEqInteger x y)   
-- 
-- 
-- instance BEq a => BEq [a] where 
--   bEq    = bEqList' 
--   reflP  = undefined  
--   symmP  = symmList 
--   transP = undefined 
-- 
-- 
-- {-@ assume bEqList' :: BEq a => xs:[a] -> ys:[a] -> {v:Bool | (v <=> bEq xs ys) && (v <=> bEqList xs ys) } @-}
-- bEqList' :: BEq a => [a] -> [a] -> Bool 
-- bEqList' = bEqList 
-- 
-- {-@ reflect bEqList @-}
-- bEqList :: BEq a => [a] -> [a] -> Bool 
-- bEqList [] [] = True 
-- bEqList (x:xs) (y:ys) = bEq x y && bEqList xs ys 
-- bEqList _ _ = False  
-- 
-- {-@ reflList :: BEq a => xs:[a] -> {bEq xs xs} @-}
-- reflList :: BEq a => [a] -> ()
-- reflList x@[]    = () `const` bEqList x x `const` bEqList' x x
-- {- reflList (x:xs) = undefined 
--   bEq (x:xs) (x:xs) ==. 
--   bEqList' (x:xs) (x:xs) ==. 
--   bEqList (x:xs) (x:xs) ==.
--   (bEq x x && bEqList xs xs)
--     ? reflP x ==.
--   bEqList xs xs ==. 
--   bEqList' xs xs 
--     ? reflList xs ==. 
--   True *** QED 
-- -}
-- 
-- {-@ symmList :: BEq a => xs:[a] -> ys:[a] -> {bEq xs ys => bEq ys xs} @-}
-- symmList :: BEq a => [a] -> [a] -> ()
-- symmList = undefined 
-- 
-- 
-- {-@ assume bEqInteger :: x:Integer -> y:Integer -> {v:Bool | (v <=> bEq x y) && (v <=> x = y)} @-} 
-- bEqInteger :: Integer -> Integer -> Bool 
-- bEqInteger x y = x == y 
