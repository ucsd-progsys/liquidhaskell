{-@ LIQUID "--reflection" @-}
{-# LANGUAGE RankNTypes   #-}

module CCC where

import Language.Haskell.Liquid.Equational 

data StackFun a b = SF (forall z. (a, z) -> (b,z))
data Pair a b = Pair a b 

firstUnfold :: (a -> b) -> a -> z -> ()
{-@ firstUnfold :: f:(a -> b) -> x:a -> y:z -> { first f (Pair x y) == Pair (f x) y } @-}
firstUnfold f x y = first f (Pair x y) ==. Pair (f x) y *** QED  


-- This fails because firstFA is encoded as having one argument 
firstUnfoldFA :: (a -> b) -> a -> z -> ()
{-@ firstUnfoldFA :: f:(a -> b) -> x:a -> y:z -> { firstFA f (Pair x y) == Pair (f x) y } @-}
firstUnfoldFA f x y = firstFA f (Pair x y) ==. Pair (f x) y *** QED  


{-@ reflect firstFA @-}
firstFA :: (a -> b) -> (forall z. (Pair a z) -> (Pair b z))
firstFA f (Pair x y) = Pair (f x) y


{-@ reflect first @-}
first :: (a -> b) -> (Pair a z) -> (Pair b z)
first f (Pair x y) = Pair (f x) y

