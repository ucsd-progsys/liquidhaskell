{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}

module Proves where

type Proof = Bool

-- proof operators requiring proof terms
infixl 3 ==:, <=:, <:

-- proof operators with optional proof terms
infixl 3 ==!, <=!, <!

-- provide the proof terms after ? 
infixl 3 ?



(<=:) :: Ord a => a -> a -> Proof -> a 
{-@ (<=:) :: x:a -> y:a -> {v:Proof | x <= y } -> {v:a | v == x } @-} 
(<=:) x y _ = x

(<:) :: Ord a => a -> a -> Proof -> a 
{-@ (<:) :: x:a -> y:a -> {v:Proof | x < y } -> {v:a | v == x } @-} 
(<:) x y _ = x


(==:) :: Eq a => a -> a -> Proof -> a 
{-@ (==:) :: (Eq a) => x:a -> y:a -> {v:Proof| x == y} -> {v:a | v == x } @-} 
(==:) x y _ = x 



class OptEq a r where
  (==!) :: a -> a -> r 

instance OptEq a (Bool -> a) where
{-@ instance OptEq a (Bool -> a) where 
  ==! :: x:a -> y:{a | x == y} -> Bool -> {v:a | v == x }
  @-}
  (==!) x _ _ = x 

instance OptEq a a where
{-@ instance OptEq a a where 
  ==! :: x:a -> y:{a| x == y} -> {v:a | v == x }
  @-}
  (==!) x y = (==!) x y True  



class OptLEq a r where
  (<=!) :: a -> a -> r 

instance OptLEq a (Bool -> a) where
{-@ instance OptLEq a (Bool -> a) where 
  <=! :: x:a -> y:a -> {v:Bool| x <= y} -> {v:a | v == x && v <= y}
  @-}
  (<=!) x _ _ = x 

instance OptLEq a a where
{-@ instance OptLEq a a where 
  <=! :: x:a -> y:{a| x <= y} -> {v:a | v == x && v <= y }
  @-}
  (<=!) x y = (<=!) x y True  


class OptLess a r where
  (<!) :: a -> a -> r 

instance OptLess a (Bool -> a) where
{-@ instance OptLess a (Bool -> a) where 
  <! :: x:a -> y:a -> {v:Bool| x < y} -> {v:a | v == x && v < y}
  @-}
  (<!) x _ _ = x 

instance OptLess a a where
{-@ instance OptLess a a where 
  <! :: x:a -> y:{a| x < y} -> {v:a | v == x && v < y }
  @-}
  (<!) x y = (<!) x y True  




(?) :: (Proof -> a) -> Proof -> a 
f ? y = f y 

proof :: Int -> Bool 
proof _ = True 