module SGD where

import Prelude hiding (elem, intersect)
import Data.Functor.Identity

{-@ type StepSize = {v:Double|0 <= v} @-}
type StepSize = Double
type DataPoint = (Double, Double)
type Weight = Double
type LossFunction = DataPoint -> [Weight] -> Double

type Set a = [a] 
type DataSet = Set DataPoint

type Distr a = Identity a
type DataDistr = Distr DataPoint

{-@ reflect diff @-}
{-@ diff :: xs:[a] -> ys:{[a]|len ys == len xs} -> {v:Double|0 <= v} @-}
diff :: Eq a => [a] -> [a] -> Double
diff (x : xs) (y : ys) | x == y = diff xs ys
diff (x : xs) (y : ys) | x /= y = 1 + diff xs ys
diff _ _                        = 0

{-@ measure dist :: a -> a -> Double @-}
dist :: a -> a -> Double
dist _ _ = 0

{-@ measure SGD.unif :: Set DataPoint -> DataDistr @-}
unif :: Set DataPoint -> DataDistr
unif = return . head

{-@ measure SGD.choice :: Double -> DataDistr -> DataDistr -> DataDistr @-}
choice :: Double -> DataDistr -> DataDistr -> DataDistr
choice p a b = a

{-@ assume relational choice ~ choice :: Double -> DataDistr -> DataDistr -> DataDistr
                                       ~ Double -> DataDistr -> DataDistr -> DataDistr
                                      ~~ dist r1 r2 <= p * k + (1 - p) * k' @-}

update :: DataDistr -> Distr [Weight] -> StepSize -> LossFunction -> Distr [Weight]
update z w α f = w

sgd :: DataSet -> Distr [Weight] -> [StepSize] -> LossFunction -> Distr [Weight]
sgd zs w0 [] f  = w0
sgd zs w0 (α:a) f 
    =   let z' = unif zs in let w' = update z' w0 α f in sgd zs w' a f
{-
    === let z' = choice (1 / length zs) (unif [z]) (unif zs0) in 
            let w'= update z' w0 α f in 
                sgd zs w' a f
        ? Unif (zs0 ++ [z]) = Choice |S|/|S++S'| Unif(S) Unif(S')
    === choice (1 / length zs) 
            (let z' = unif [z] in sgd zs (update z' w0 α f) a f) 
            (let z' = unif zs0 in sgd zs (update z' w0 α f) a f)
        ? let z=Choice p mu mu' in e === Choice p (let z=mu in e) (let z=mu' in e)` 
-}

{-@ measure lend @-}
lend :: [a] -> Double
lend [] = 0
lend (_:xs) = 1 + lend xs

{-@ reflect disjunion @-}
disjunion :: [DataPoint] -> [DataPoint] -> [DataPoint]
disjunion [] ys = ys
disjunion (x:xs) ys | elem x ys = disjunion xs ys
disjunion (x:xs) ys = x : disjunion xs ys

{-@ inline axiom @-}
axiom :: [DataPoint] -> [DataPoint] -> Bool
axiom zs zs' = unif (disjunion zs zs') == choice (lend zs / lend (disjunion zs zs')) (unif zs) (unif zs')

-- axiom' zs1 zs2 = unif zs1 == choice (lend (intersect zs1 zs2) / lend zs1) (intersect zs1 zs2) (minus zs1 zs2)
-- axiom'' = let z = choice p mu mu' in e ~> choice p (let z = mu in e) (let z = mu' in e)

{-@ reflect elem @-}
elem :: DataPoint -> DataSet -> Bool
elem _ [] = False
elem y (x:xs) = y == x || elem y xs

{-@ reflect intersect @-}
intersect :: DataSet -> DataSet -> DataSet
intersect [] _ = []
intersect (y:ys) xs | elem y xs = y : intersect ys xs
intersect (_:ys) xs = intersect ys xs

{-@ reflect minus @-}
minus :: DataSet -> DataSet -> DataSet
minus [] xs = []
minus (y:ys) xs | elem y xs = minus ys xs
minus (y:ys) xs = y : minus xs ys

{-
SGD.axiom (SGD.intersect zs1 zs2) (SGD.minus zs1 zs2) && 
                                SGD.axiom (SGD.intersect zs1 zs2) (SGD.minus zs2 zs1) |-
-}

{-@ reflect div @-}
div :: Double -> Double -> Double
div a b = a / b

type Sgd = DataSet -> Distr [Weight] -> [StepSize] -> LossFunction -> Distr [Weight] 

pred :: DataSet -> DataSet -> Sgd -> Sgd -> Distr [Weight] -> Distr [Weight] -> [StepSize] -> [StepSize] -> LossFunction -> LossFunction -> Bool
pred zs1 zs2 r1 r2 ws1 ws2 α1 α2 f1 f2 = 
    SGD.unif zs1 == SGD.choice (SGD.lend (SGD.intersect zs1 zs2) / SGD.lend zs1) 
                                (SGD.unif (SGD.intersect zs1 zs2)) (SGD.unif (SGD.minus zs1 zs2)) &&
        SGD.unif zs2 == SGD.choice (SGD.lend (SGD.intersect zs2 zs1) / SGD.lend zs2) 
                                    (SGD.unif (SGD.intersect zs2 zs1)) (SGD.unif (SGD.minus zs2 zs1)) &&
            length zs1 == length zs2 && 
                dist (r1 zs1 ws1 α1 f1) (r2 zs2 ws2 α2 f2) <= dist ws1 ws2 + 2.0 * SGD.diff zs1 zs2

{-@ relational sgd ~ sgd :: zs1:DataSet -> ws1:Distr [Weight] -> α1:[StepSize] -> f1:LossFunction -> v:Distr [Weight] 
                          ~ zs2:DataSet -> ws2:Distr [Weight] -> α2:[StepSize] -> f2:LossFunction -> v:Distr [Weight]
                         ~~ SGD.axiom (SGD.intersect zs1 zs2) (SGD.minus zs1 zs2) && 
                                SGD.axiom (SGD.intersect zs1 zs2) (SGD.minus zs2 zs1) |-
                                    len zs1 = len zs2 => true => true => true =>
                                        dist (r1 zs1 ws1 α1 f1) (r2 zs2 ws2 α2 f2) <= 
                                            dist ws1 ws2 + 2.0 * SGD.diff zs1 zs2 @-}
