module TrClosure where

import Language.Haskell.Liquid.Prelude
import LiquidArray

{-@ tclosure :: forall <p :: x0:Int -> Bool>.
              (Int<p> -> [Int]<p>) -> [Int<p>]-> Int<p> -> [Int<p>]@-}
tclosure a dom = if old == new then a else tclosure a' dom
  where old = map (\i -> get i a ) dom
        new = map (\i -> get i a') dom
        a'  = tclose1 a dom

tclose1 :: (Int -> [Int]) -> [Int] -> (Int -> [Int])
tclose1 = myfoldr (\i a -> set i (getconcat (get i a) a []) a)
  where  getconcat []     a ack = ack
         getconcat (i:is) a ack = getconcat is a (ack ++ get i a) 

myfoldr f b []     = b
myfoldr f b (x:xs) = f x (myfoldr f b xs)

graph1 = empty
graph2 = set 1 [1] empty
graph3 = set 2 [1] (set 1 [1, 2] empty)

prop1 = tclosure graph1 []
prop2 = tclosure graph2 [1]
prop3 = tclosure graph3 [1, 2]
















