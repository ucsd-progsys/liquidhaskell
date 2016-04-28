{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
module Optional where


class Eq a => OptEq a r where
  (===) :: a -> a -> Bool -> r 

instance Eq a => OptEq a a where
{-@ instance OptEq a a where 
  (===) :: a -> a -> Bool -> a
  @-}
  (===) x _ _ = x 

instance Eq a => OptEq a (Bool -> a) where
  (===) x _ _ _ = x 

{- 
bar :: Char 
bar = (===) 'c' 'y' True 

foo :: Bool -> Char 
foo x = (===) 'c' 'y' x 
-}

{- $dOptEq_aLA :: a -> a -> Bool -> a @-}
{- 
class Optional1 x a b r where 
  opt1 :: (x -> x -> a -> b) -> x -> x -> a -> r

instance Optional1 x a b b where
  opt1 f x y z = f x y z

instance Optional1 x a b (a -> b) where
  opt1 f x y _ = f x y  

bar :: (Eq a, Optional1 a Bool a r) => a -> a -> r
bar x y = opt1 (==:) x y True 

(==:) :: Eq a =>  a -> a -> Bool -> a 
{- (==:) :: x:a -> y:a -> {v:Bool| x == y} -> {v:a | v == x } @-} 
(==:) x y _ = x 

-}