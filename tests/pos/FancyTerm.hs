{-# LANGUAGE GADTs #-}
module FancyTerm where 

import Language.Haskell.Liquid.This

data Tree a where 
    Leaf :: a -> Tree a 
    Node :: (Int -> (Tree a)) -> Tree a 

{-@ measure tsize :: Tree a -> Nat @-}

{-@ data Tree a where 
      Leaf :: a -> {t:Tree a  | tsize t == 0 } 
      Node :: f:(Int -> ({tt:Tree a | tsize tt < tsize this && 0 <= tsize tt })) 
           -> {t:Tree a | 0 <= tsize t}  @-}

{-@ mapTr :: (a -> a) -> t:Tree a -> o:Tree a / [tsize t] @-}
mapTr :: (a -> a) -> Tree a -> Tree a 
mapTr f (Leaf x) = Leaf $ f x 
mapTr f (Node n) = Node (\x -> mapTr f (n x)) 



-- With Nat invariant 
{-@ measure itsize :: ITree a -> Nat @-}
{-@ invariant {t:ITree a | 0 <= itsize t} @-}

data ITree a where 
    ILeaf :: a -> ITree a 
    INode :: (Int -> (ITree a)) -> ITree a 

{-@ data ITree a where 
      ILeaf :: a -> {t:ITree a  | itsize t == 0 } 
      INode :: f:(Int -> ({tt:ITree a | itsize tt < itsize this})) 
            -> ITree a  @-}

{-@ imapTr :: (a -> a) -> t:ITree a -> o:ITree a / [itsize t] @-}
imapTr :: (a -> a) -> ITree a -> ITree a 
imapTr f (ILeaf x) = ILeaf $ f x 
imapTr f (INode n) = INode (\x -> imapTr f (n x)) 
