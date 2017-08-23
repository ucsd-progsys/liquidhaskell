module ORM where

{-@ LIQUID "--exactdc"  @-}
{-@ LIQUID "--higherorder" @-}


import Prelude hiding (length, filter)
import Language.Haskell.Liquid.ProofCombinators

--  here is a "user" query
{-@ prop :: L Row -> L {v:Row | rowLeft v == 5} @-}
prop :: L Row -> L Row
prop xs = mapCast evalQProp $ filter (evalQ (Qry Eq Fst (Const 5))) xs


{-@ prop0 :: L Row -> L {v:Row | evalQ (Qry Eq Fst (Const 5)) v} @-}
prop0 :: L Row -> L Row
prop0 xs = filter (evalQ (Qry Eq Fst (Const 5))) xs

{-@ mapCast :: (x:Row -> {evalQ (Qry Eq Fst (Const 5)) x <=> rowLeft x == 5})
            -> L {v:Row | evalQ (Qry Eq Fst (Const 5)) v}
            -> L {v:Row | rowLeft v == 5} @-}
mapCast :: (Row -> Proof) -> L Row -> L Row
mapCast _ N = N
mapCast p (C x xs) = cast (p x) x `C` mapCast p xs



evalQProp :: Row -> Proof
{-@ evalQProp :: x:Row -> {evalQ (Qry Eq Fst (Const 5)) x <=> rowLeft x == 5} @-}
evalQProp (Row l r)
  =   evalQ (Qry Eq Fst (Const 5)) (Row l r)
  ==. evalC Eq (evalV Fst (Row l r)) (evalV (Const 5) (Row l r))
  ==. evalC Eq l 5
  ==. l == 5
  *** QED



--  here is the DB API (will add more detail later but its pretty self contained)

data Cmp = Eq | Ne
{-@ data Cmp = Eq | Ne @-}

data Val = Const {valConst :: Int} | Fst | Snd
{-@ data Val = Const {valConst :: Int} | Fst | Snd @-}

data Qry = Qry {qryCmp :: Cmp, qryLHS :: Val, qryRHS :: Val }

{-@ data Qry = Qry {qryCmp :: Cmp, qryLHS :: Val, qryRHS :: Val } @-}

data Row = Row {rowLeft :: Int, rowRigth :: Int}
{-@ data Row = Row {rowLeft :: Int, rowRigth :: Int} @-}

data L a = N | C {hd :: a, tl :: L a}
{-@ data L [length] a = N | C {hd :: a, tl :: L a} @-}

length :: L a -> Int
{-@ length :: L a -> Nat @-}
{-@ measure length @-}
length N = 0
length (C _ xs) = 1 + length xs

------------------------------------------------------------------------
{-@ reflect evalQ @-}
evalQ :: Qry -> Row -> Bool
evalQ (Qry o v1 v2) r = evalC o (evalV v1 r) (evalV v2 r)

{-@ reflect evalV @-}
evalV :: Val -> Row -> Int
evalV (Const n) _         = n
evalV Fst       (Row l _) = l
evalV Snd       (Row _ r) = r

{-@ reflect evalC @-}
evalC :: Cmp -> Int -> Int -> Bool
evalC Eq x y = x == y
evalC Ne x y = x /= y

{-@ reflect filterQ @-}
filterQ :: Qry -> L Row -> L Row
filterQ qry xs = filter (evalQ qry) xs


{-@ reflect filter @-}
{-@ filter :: forall <p :: a -> Bool, w :: a -> Bool -> Bool>.
                  {x::a , b::{v:Bool<w x> | v} |- {v:a | v == x} <: a<p> }
                  (x:a -> Bool<w x>) -> L a -> L (a<p>)
  @-}
filter :: (a -> Bool) -> L a -> L a
filter _ N = N
filter p (C x xs)
  | p x       = x `C` filter p xs
  | otherwise = filter p xs
