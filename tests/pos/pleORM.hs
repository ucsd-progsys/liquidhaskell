module ORM where

{- LIQUID "--no-adt" 	      @-}
{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple"            @-}

import Prelude hiding (length, filter)

--  here is a "user" query
{-@ prop0 :: [Row] -> [{v:Row | rowLeft v == 5}] @-}
prop0 :: [Row] -> [Row]
prop0 = filterQ (Qry Eq Fst (Const 5))

{-@ prop1 :: [Int] -> [{v:Int | v == 10}] @-}
prop1 :: [Int] -> [Int]
prop1 = filterQQ (QQ 10)

{-@ prop2 :: [Int] -> [{v:Int | v == 10}] @-}
prop2 :: [Int] -> [Int]
prop2 = filterQQ (mkQQ 10)

{-@ reflect mkQQ @-}
mkQQ :: Int -> QQ
mkQQ n = QQ n

{-@ filterQ :: q:Qry -> [Row] -> [{v:Row | evalQ q v}] @-}
filterQ :: Qry -> [Row] -> [Row]
filterQ q = filter (evalQ q)

{-@ filterQQ :: q:QQ -> [Int] -> [{v:Int | evalQQ q v}] @-}
filterQQ :: QQ -> [Int] -> [Int]
filterQQ q = filter (evalQQ q)


--------------------------------------------------------------------------------
-- | DB API
--------------------------------------------------------------------------------

data Cmp = Eq | Ne
data Val = Const Int | Fst | Snd
data Qry = Qry Cmp Val Val

data QQ  = QQ Int


data Row = Row {rowLeft :: Int, rowRight :: Int}
{-@ data Row = Row {rowLeft :: Int, rowRight :: Int} @-}

{-@ reflect evalQQ @-}
evalQQ :: QQ -> Int -> Bool
evalQQ (QQ x) y = x == y

{-@ reflect evalQ @-}
evalQ :: Qry -> Row -> Bool
evalQ (Qry o v1 v2) r = evalC o (evalV v1 r) (evalV v2 r)

{-@ reflect evalV @-}
evalV :: Val -> Row -> Int
evalV (Const n) _ = n
evalV Fst       r = rowLeft  r
evalV Snd       r = rowRight r

{-@ reflect evalC @-}
evalC :: Cmp -> Int -> Int -> Bool
evalC Eq x y = x == y
evalC Ne x y = x /= y

--------------------------------------------------------------------------------
-- | Generic List API
--------------------------------------------------------------------------------

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []
