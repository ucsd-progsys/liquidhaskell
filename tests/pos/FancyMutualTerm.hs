{-# LANGUAGE GADTs #-}
module FancyMutualTerm where 

import Language.Haskell.Liquid.This

{-@ measure tsize :: Tree a -> Nat @-}
{-@ data size (Tree a) tsize @-}

data Tree a where 
    Leaf :: a -> Tree a 
    Node :: (Int -> (Tree a)) -> Tree a 

{-@ data Tree a where 
      Leaf :: a -> {t:Tree a  | tsize t == 0 } 
      Node :: f:(Int -> Tree a) -> Tree a  @-}


{-@ mapTr :: (a -> a) -> t:Tree a -> Tree a / [tsize t, 2] @-}
mapTr :: (a -> a) -> Tree a -> Tree a 
mapTr f (Leaf x) = Leaf (f x) 
mapTr f d@(Node n) = Node (mapTr2 d f n)


{-@ mapTr2 :: t:Tree a -> (a -> a) -> (Int -> {tt:Tree a | tsize tt < tsize t }) -> Int -> Tree a / [tsize t, 1] @-} 
mapTr2 :: Tree a -> (a -> a) -> (Int -> Tree a) -> Int -> Tree a  
mapTr2 _ f n x = mapTr f (n x)


