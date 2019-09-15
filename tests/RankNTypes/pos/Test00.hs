{-@ LIQUID "--reflection" @-}
{-# LANGUAGE RankNTypes   #-}

module Test00 where

import Language.Haskell.Liquid.Equational 

data StackFun a b = SF (forall z. (a, z) -> (b,z))
data Test a b = Test (forall z. z)
data Pair a b = Pair a b 


{- 
firstUnfold :: (a -> b) -> a -> z -> ()
{-@ firstUnfold :: f:(a -> b) -> x:a -> y:z -> { first f (Pair x y) == Pair (f x) y } @-}
firstUnfold f x y = first f (Pair x y) ==. Pair (f x) y *** QED  

{-@ reflect firstFA @-}
firstFA :: (a -> b) -> (forall z. (Pair a z) -> (Pair b z))
firstFA f (Pair x y) = Pair (f x) y


{-@ reflect first @-}
first :: (a -> b) -> (Pair a z) -> (Pair b z)
first f (Pair x y) = Pair (f x) y
-}

