
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Query where

import Prelude hiding (filter)

data Atom  = VarX
           | VarY
           | Const Int

data Query = Le  Atom  Atom
           | And Query Query
           | Or  Query Query

{-@ data Blob  = B { xVal :: Int, yVal :: Int } @-}
data Blob  = B { xVal :: Int, yVal :: Int }

{-@ reflect evalA @-}
evalA :: Atom -> Blob -> Int
evalA VarX  b     = xVal b
evalA VarY  b     = yVal b
evalA (Const n) _ = n

{-@ reflect evalQ @-}
evalQ :: Query -> Blob -> Bool
evalQ (Le  a1 a2) b = (evalA a1 b) <= (evalA a2 b)
evalQ (And q1 q2) b = (evalQ q1 b) && (evalQ q2 b)
evalQ (Or  q1 q2) b = (evalQ q1 b) || (evalQ q2 b)

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []

{-@ filterQ :: q:Query -> [Blob] -> [{b:Blob | evalQ q b}] @-}
filterQ :: Query -> [Blob] -> [Blob]
filterQ q = filter (evalQ q) 

{-@ test1 :: [Blob] -> [{v: Blob | xVal v <= 10}] @-}
test1   = filterQ q1
  where
  q1    = (VarX `Le` (Const 10))

{-@ test2 :: [Blob] -> [{v: Blob | xVal v <= 10 && yVal v <= 20}] @-}
test2  = filterQ q2
  where
  q2   = (VarX `Le` (Const 10)) `And` (VarY `Le` (Const 20))

{- filterQ :: q:Query -> [Blob] -> [{b:Blob | evalQ q b}] @-}
-- filterQ :: Query -> [Blob] -> [Blob]
-- filterQ q []     = []
-- filterQ q (b:bs)
-- /  | evalQ q b    = b : filterQ q bs
-- /  | otherwise    =     filterQ q bs
