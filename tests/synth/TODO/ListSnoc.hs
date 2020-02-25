{-@ LIQUID "--typed-holes" @-}
-- {-# LANGUAGE ScopedTypeVariables #-}
module ListSnoc where

import qualified Data.Set as S
import Language.Haskell.Liquid.Synthesize.Error

-- data List a <p :: a -> a -> Bool> where
-- 	Nil :: List a <p>
-- 	Cons :: x: a -> xs: List {a | p x _v} <p> -> List a <p>
-- {-@ 
--     data L a <p :: a -> a -> Bool> 
--         = N | C { x :: a, xs :: L <p> (a<p x>) }
    
--   @-}
-- data L a = N | C a (L a)

-- {-@ measure lElts @-}
-- {-@ lElts :: L a -> S.Set a @-}
-- lElts :: Ord a => L a -> S.Set a
-- lElts N        = S.empty
-- lElts (C x xs) = S.union (S.singleton x) (lElts xs)

-- {-@ measure length' @-}
-- {-@ length' :: L a -> Nat @-}
-- length' :: L a -> Int 
-- length' N        = 0
-- length' (C x xs) = 1 + length' xs

-- {-@ snoc :: forall a <p :: a -> a -> Bool>.
--                 x:a -> xs:  L <p> (a<p x>) 
--                     -> {v: L <p> a |   length' v == length' xs + 1 && 
--                                         S.union (S.singleton x) (lElts xs) == lElts v}
--   @-}
-- snoc :: a -> L a -> L a
-- -- snoc = _goal
-- -- snoc x xs = C x xs
-- snoc x xs = 
--     case xs of
--       N    -> C x N
--       C x5 x6 -> C x5 (snoc x x6)

-- {-@ snoc' :: forall <p :: a -> a -> Bool>. x:a -> [a<p x>]<p> -> [a]<p> @-}
-- snoc' :: a -> [a] -> [a]
-- snoc' x [] = [x]
-- snoc' x (y:ys) = y:snoc' x ys


{-@ snoc' :: forall <p :: a -> a -> Bool, q:: a -> a -> Bool>. 
             {x::a, y::a |- {v:a<q y> | v == x }<: {v:a<p x> | v == y} }
             {x::a, y::a |- {v:a<p y> | v == x }<: {v:a<q x> | v == y} }
             x:a -> xs: [(a<q x>)]<p> -> 
                 { v: ([a]<p>) |    len v == len xs + 1}
  @-}
snoc' :: a -> [a] -> [a]
snoc' = _goal


{-

forall x y. q y x => p x y  

forall x. q x x <=> p x x 


p x v 
p v x

-}



-- snoc' x xs = x : xs

-- snoc' x [] = [x]
-- snoc' x (y:ys) = y:snoc' x ys 

-- This is SAFE.
-- snoc' x [] = [x]
-- snoc' x (y:ys) = y:snoc' x ys 




