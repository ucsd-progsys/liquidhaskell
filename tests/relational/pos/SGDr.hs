module SGDr where

import           Prelude                 hiding ( head
                                                , tail
                                                )
import           Data.Functor.Identity


import           Language.Haskell.Liquid.ProofCombinators

{-@ type Prob = {v:Double|0 <= v && v <= 1} @-}
type Prob = Double

type StepSize = Double
type DataPoint = (Double, Double)
type Weight = Double
type LossFunction = DataPoint -> Weight -> Double

type Set a = [a]
{-@ type DataSet = {v:Set DataPoint|0 < len v && 0 < lend v } @-}
type DataSet = Set DataPoint
type Distr a = a
type DataDistr = Distr DataPoint

{-@ measure dist :: a -> a -> Double @-}
{-@ dist :: x1:a -> x2:a -> {v:Double | v == dist x1 x2 } @-}
dist :: a -> a -> Double
dist _ _ = undefined

{-@ assume relational choice ~ choice 
        :: p:_ -> e1:_ -> e1':_ -> _
         ~ q:_ -> e2:_ -> e2':_ -> _
        ~~ p = q => true => true => 
            dist (r1 p e1 e1') (r2 q e2 e2') <= p * (dist e1 e2) + (1 - p) * (dist e1' e2') @-}

{-@ choice :: Prob -> Distr a -> Distr a -> Distr a @-}
choice :: Prob -> Distr a -> Distr a -> Distr a
choice _ x _ = x

unif :: DataSet -> DataDistr
unif = undefined

{-@ assume relational update ~ update 
      :: z1:_ -> ws1:_ -> α1:_ -> f1:_ -> _ 
       ~ z2:_ -> ws2:_ -> α2:_ -> f2:_ -> _
      ~~ true => true => α1 = α2 => f1 = f2 => 
          dist (r1 z1 ws1 α1 f1) (r2 z2 ws2 α2 f2) = dist ws1 ws2 @-}

{-@ assume relational update ~ update 
      :: z1:_ -> ws1:_ -> α1:_ -> f1:_ -> _ 
       ~ z2:_ -> ws2:_ -> α2:_ -> f2:_ -> _
      ~~ z1 = z2 => true => α1 = α2 => f1 = f2 => 
          dist (r1 z1 ws1 α1 f1) (r2 z2 ws2 α2 f2) = dist ws1 ws2 @-}

update :: DataPoint -> Weight -> StepSize -> LossFunction -> Weight
update = undefined

{-@ reflect one @-}
{-@ one :: {v:Double|v = 1} @-}
one :: Double
one = 1

{-@ measure lend @-}
{-@ lend :: xs:[a] -> {v:Double|v >= 0} @-}
lend :: [a] -> Double
lend []       = 0
lend (_ : xs) = 1 + lend xs

{-@ assume relational pbind ~ pbind :: ws1:_ -> e1:_ -> f1:_ -> _
                                     ~ ws2:_ -> e2:_ -> f2:_ -> _
                                    ~~ true => true => 
                                        dist (f1 e1) (f2 e2) <= dist ws1 ws2 => 
                                          dist (r1 e1 f1) (r2 e2 f2) = dist ws1 ws2 @-}

{-@ assume relational qbind ~ qbind :: ws1:_ -> e1:_ -> f1:_ -> _
                                     ~ ws2:_ -> e2:_ -> f2:_ -> _
                                    ~~ true => e1 = e2 => 
                                        dist (f1 e1) (f2 e2) <= dist ws1 ws2 => 
                                          dist (r1 e1 f1) (r2 e2 f2) = dist ws1 ws2 @-}

pbind :: Weight -> Distr a -> (a -> Distr b) -> Distr b
pbind = undefined

qbind :: Weight -> Distr a -> (a -> Distr b) -> Distr b
qbind = undefined

{-@ reflect ppure @-}
ppure :: a -> Distr a
ppure x = x

{-@ reduce :: p:Double -> ws1:Weight -> ws2:Weight -> {p * dist ws1 ws2 + (1 - p) * dist ws1 ws2 = dist ws1 ws2} @-}
reduce :: Double -> Weight -> Weight -> ()
reduce _ _ _ = ()

{-@ reflect head @-}
{-@ head :: {xs:[a] | len xs > 0 } -> a @-}
head :: [a] -> a
head (z : _) = z

{-@ reflect tail @-}
{-@ tail :: {xs:[a] | len xs > 0 } -> {v:[a] | len v == len xs - 1 && lend v == lend xs - 1 } @-}
tail :: [a] -> [a]
tail (_ : zs) = zs

{-@ sgd :: zs:{DataSet | 1 < len zs && 1 < lend zs } -> Weight -> [StepSize] -> LossFunction -> Distr Weight @-}
sgd :: DataSet -> Weight -> [StepSize] -> LossFunction -> Distr Weight
sgd _  w0 []      _ = ppure w0
sgd zs w0 (α : a) f = choice (one / lend zs)
                              (pbind w0 uhead upd)
                              (qbind w0 utail upd)
 where
  upd z' = sgd zs (update z' w0 α f) a f
  uhead = unif [head zs]
  utail = unif (tail zs)

{-@ relational sgd ~ sgd :: zs1:{DataSet | 1 < lend zs1 && 1 < len zs1} -> ws1:_ -> α1:_ -> f1:_ -> _ 
                            ~ zs2:{DataSet | 1 < lend zs2 && 1 < len zs2} -> ws2:_ -> α2:_ -> f2:_ -> _
                           ~~ SGDr.lend zs1 == SGDr.lend zs2 && SGDr.tail zs1 = SGDr.tail zs2 =>
                                true => α2 = α1 => true => 
                                  SGDr.dist (r1 zs1 ws1 α1 f1) (r2 zs2 ws2 α2 f2) <= 
                                    (SGDr.one / (SGDr.lend zs1)) * (SGDr.dist ws1 ws2) + 
                                      (1 - (SGDr.one / (SGDr.lend zs1))) * (SGDr.dist ws1 ws2)
@-}
