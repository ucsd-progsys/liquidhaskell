{-# LANGUAGE GADTs #-}
module FancyTerm where 


data Tree a where 
    Leaf :: a -> Tree a 
    Node :: (Int -> (Tree a)) -> Tree a 

{-@ measure tsize :: Tree a -> Nat @-}
{-@ data size (Tree a) tsize @-}

{-@ data Tree a where 
      Leaf :: a -> {t:Tree a  | tsize t == 0 } 
      Node :: f:(Int -> Tree a) -> Tree a   @-}

{-@ mapTr :: (a -> a) -> t:Tree a -> o:Tree a / [tsize t] @-}
mapTr :: (a -> a) -> Tree a -> Tree a 
mapTr f (Leaf x) = Leaf $ f x 
mapTr f (Node n) = Node (\x -> mapTr f (n x)) 



-- With Nat invariant 
{-@ measure itsize :: ITree a -> Nat @-}
{-@ data size (ITree a) itsize @-}

data ITree a where 
    ILeaf :: a -> ITree a 
    INode :: (Int -> ITree a) -> ITree a 

{-@ data ITree a where 
      ILeaf :: a -> {t:ITree a  | itsize t == 0 } 
      INode :: f:(Int -> ITree a) 
            -> ITree a  @-}

{-@ imapTr :: (a -> a) -> t:ITree a -> o:ITree a / [itsize t] @-}
imapTr :: (a -> a) -> ITree a -> ITree a 
imapTr f (ILeaf x) = ILeaf $ f x 
imapTr f (INode n) = INode (\x -> imapTr f (n x)) 
