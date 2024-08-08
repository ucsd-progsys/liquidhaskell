-- | Check the behavior of reflection from interface files with user-defined decreasing sizes
{-# LANGUAGE GADTs #-}

-- Note: this pragma is needed so that the unfoldings end up in the
-- interface files, even with `-O0`
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

-- Note that we don't export Tree here
module ReflExt07B (leftMostEl) where

data Tree a where 
    Leaf :: a -> Tree a 
    Node :: (Int -> (Tree a)) -> Tree a 

{-@ measure tsize :: Tree a -> Nat @-}
{-@ data size (Tree a) tsize @-}

{-@ data Tree a where 
      Leaf :: a -> {t:Tree a  | tsize t == 0 } 
      Node :: f:(Int -> Tree a) -> Tree a   @-}

-- Force leftMostEl to end up in the unfoldings
{-# INLINE leftMostEl #-}
{-@ leftMostEl :: t:Tree a -> a / [tsize t] @-}
leftMostEl :: Tree a -> a
leftMostEl (Leaf x) = x
leftMostEl (Node n) = leftMostEl (n 0)