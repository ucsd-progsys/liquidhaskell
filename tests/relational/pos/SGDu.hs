module SGDu where

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

{-@ relationalchoice :: p:Prob -> e1:Distr a -> e1':Distr a 
        ->  q:{Prob | p = q } -> e2:Distr a -> e2':Distr a 
        ->  {p = q => dist (choice p e1 e1') (choice q e2 e2') <= p * (dist e1 e2) + (1 - p) * (dist e1' e2')} @-}
relationalchoice :: Prob -> Distr a -> Distr a -> Prob -> Distr a -> Distr a -> ()
relationalchoice _ _ _ _ _ _ = undefined

{-@ measure SGDu.choice :: Prob -> Distr a -> Distr a -> Distr a @-}
{-@ assume choice :: x1:Prob -> x2:Distr a -> x3:Distr a -> {v:Distr a |  v == choice x1 x2 x3 } @-}
choice :: Prob -> Distr a -> Distr a -> Distr a
choice _ x _ = x

{-@ measure SGDu.unif :: zs:DataSet -> DataDistr @-}
{-@ assume unif :: x:DataSet -> {v:DataDistr | v == unif x } @-}
unif :: DataSet -> DataDistr
unif = undefined

{-@ relationalupdatep :: z1:DataPoint -> ws1:Weight -> α1:StepSize -> f1:LossFunction -> 
                                  z2:DataPoint -> ws2:Weight -> {α2:StepSize|α1 = α2} -> {f2:LossFunction|f1 = f2} -> 
                                    {dist (update z1 ws1 α1 f1) (update z2 ws2 α2 f2) = dist ws1 ws2} @-}
relationalupdatep :: DataPoint -> Weight -> StepSize -> LossFunction -> DataPoint -> Weight -> StepSize -> 
  LossFunction -> ()
relationalupdatep = undefined


{-@ relationalupdateq :: z1:DataPoint -> ws1:Weight -> α1:StepSize -> f1:LossFunction -> 
                                  {z2:DataPoint|z1 = z2} -> ws2:Weight -> {α2:StepSize|α1 = α2} -> {f2:LossFunction|f1 = f2} -> 
                                    {dist (update z1 ws1 α1 f1) (update z2 ws2 α2 f2) = dist ws1 ws2} @-}
relationalupdateq :: DataPoint -> Weight -> StepSize -> LossFunction -> DataPoint -> Weight -> StepSize -> 
  LossFunction -> ()
relationalupdateq = undefined

{-@ measure SGDu.update :: DataPoint -> Weight -> StepSize -> LossFunction -> Weight @-}
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

-- TODO: diamond
{-@ relationalpbind :: ws1:Weight -> ws2:Weight -> e1:Distr a -> f1:(a -> Distr b) -> e2:Distr a -> f2:(a -> Distr b) -> 
        {v:() | dist (f1 e1) (f2 e2) <= dist ws1 ws2 } -> 
        { dist (pbind e1 f1) (pbind e2 f2) = dist ws1 ws2 } @-}
relationalpbind :: Weight -> Weight -> Distr a -> (a -> Distr b) -> Distr a -> (a -> Distr b) -> () -> ()
relationalpbind = undefined

{-@ relationalqbind :: ws1:Weight -> ws2:Weight -> e1:Distr a -> f1:(a -> Distr b) -> {e2:Distr a | e1 = e2} -> f2:(a -> Distr b) -> 
        { dist (qbind e1 f1) (qbind e2 f2) = dist ws1 ws2} @-}
relationalqbind :: Weight -> Weight -> Distr a -> (a -> Distr b) -> Distr a -> (a -> Distr b) -> ()
relationalqbind = undefined

{-@ measure SGDu.pbind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume pbind :: x1:Distr a -> x2:(a -> Distr b) -> {v:Distr b | v = pbind x1 x2 } @-}
pbind :: Distr a -> (a -> Distr b) -> Distr b
pbind = undefined

{-@ measure SGDu.qbind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume qbind :: x1:Distr a -> x2:(a -> Distr b) -> {v:Distr b | v = qbind x1 x2 } @-}
qbind :: Distr a -> (a -> Distr b) -> Distr b
qbind = undefined

{-@ reflect ppure @-}
ppure :: a -> Distr a
ppure x = x

{-@ reduce :: p:Double -> ws1:Weight -> ws2:Weight -> {p * dist ws1 ws2 + (1 - p) * dist ws1 ws2 = dist ws1 ws2} @-}
reduce :: Double -> Weight -> Weight -> ()
reduce _ _ _ = ()

{-@ assume relationalupd :: zs1:DataSet -> ws1:Weight -> α1:StepSize -> as1:[StepSize] -> f1:LossFunction -> z1:DataPoint -> 
            zs2:DataSet -> ws2:Weight -> α2:StepSize -> as2:[StepSize] -> f2:LossFunction -> z2:DataPoint -> 
              {dist (upd zs1 ws1 α1 as1 f1 z1) (upd zs2 ws2 α2 as2 f2 z2) <= dist ws1 ws2}
@-}
relationalupd :: DataSet -> Weight -> StepSize -> [StepSize] -> LossFunction -> DataPoint -> 
  DataSet -> Weight -> StepSize -> [StepSize] -> LossFunction -> DataPoint -> () 
relationalupd = undefined


{-@ reflect upd @-}
{-@ upd :: zs:{DataSet | 1 < len zs  && 1 < lend zs } -> Weight -> StepSize -> [StepSize] -> LossFunction -> DataPoint -> Distr Weight @-}
upd :: DataSet -> Weight -> StepSize -> [StepSize] -> LossFunction -> DataPoint -> Distr Weight
upd zs w0 α a f z' = sgd zs (update z' w0 α f) a f

{-@ reflect head @-}
{-@ head :: {xs:[a] | len xs > 0 } -> a @-}
head :: [a] -> a
head (z : _) = z

{-@ reflect tail @-}
{-@ tail :: {xs:[a] | len xs > 0 } -> {v:[a] | len v == len xs - 1 && lend v == lend xs - 1 } @-}
tail :: [a] -> [a]
tail (_ : zs) = zs

{-@ reflect sgd @-}
{-@ sgd :: zs:{DataSet | 1 < len zs && 1 < lend zs } -> Weight -> [StepSize] -> LossFunction -> Distr Weight @-}
sgd :: DataSet -> Weight -> [StepSize] -> LossFunction -> Distr Weight
sgd _  w0 []      _ = ppure w0
sgd zs w0 (α : a) f = choice (one / lend zs)
                             (pbind uhead (upd zs w0 α a f))
                             (qbind utail (upd zs w0 α a f))
 where
  uhead = unif [head zs]
  utail = unif (tail zs)

{-@ relationalunif :: zs1:[DataPoint] -> zs2:[DataPoint] -> {unif zs1 = unif zs2} @-}
relationalunif :: [DataPoint] -> [DataPoint] -> ()
relationalunif = undefined

{-@ thm :: zs1:{DataSet | 1 < lend zs1 && 1 < len zs1 } -> ws1:Weight -> α1:[StepSize] -> f1:LossFunction -> 
           zs2:{DataSet | 1 < lend zs2 && 1 < len zs2 && lend zs1 == lend zs2 }  -> ws2:Weight -> {α2:[StepSize]|len α2 = len α1} -> f2:LossFunction -> 
            {SGDu.lend zs1 = SGDu.lend zs2 && (SGDu.lend zs1) > 1 => 
                f1 = f2 => (SGDu.lend α2 = SGDu.lend α1) =>
                    dist (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2) <= 
                        (SGDu.one / (SGDu.lend zs1)) * (dist ws1 ws2) + (1 - (SGDu.one / (SGDu.lend zs1))) * (dist ws1 ws2)} @-}
thm :: DataSet -> Weight -> [StepSize] -> LossFunction -> DataSet -> Weight -> [StepSize] -> LossFunction -> ()
thm zs1 ws1 α1@[] f1 zs2 ws2 α2@[] f2 =
  dist (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2)
    === dist (ppure ws1) (ppure ws2)
    === dist ws1         ws2
    =<= (SGDu.one / (SGDu.lend zs1))
    *   (dist ws1 ws2)
    +   (1 - (SGDu.one / (SGDu.lend zs1)))
    *   (dist ws1 ws2)
    *** QED
thm zs1 ws1 as1@(α1 : a1) f1 zs2 ws2 as2@(α2 : a2) f2 =
  dist (sgd zs1 ws1 as1 f1) (sgd zs2 ws2 as2 f2)
    === dist
          (choice (one / lend zs1)
                  (pbind uhead1 (upd zs1 ws1 α1 a1 f1))
                  (qbind utail1 (upd zs1 ws1 α1 a1 f1))
          )
          (choice (one / lend zs2)
                  (pbind uhead2 (upd zs2 ws2 α2 a2 f2))
                  (qbind utail2 (upd zs2 ws2 α2 a2 f2))
          )
    ?   relationalchoice (one / lend zs1)
                         (pbind uhead1 (upd zs1 ws1 α1 a1 f1))
                         (qbind utail1 (upd zs1 ws1 α1 a1 f1))
                         (one / lend zs2)
                         (pbind uhead2 (upd zs2 ws2 α2 a2 f2))
                         (qbind utail2 (upd zs2 ws2 α2 a2 f2))
    =<= ( (one / lend zs1)
        * (dist (pbind uhead1 (upd zs1 ws1 α1 a1 f1))
                (pbind uhead2 (upd zs2 ws2 α2 a2 f2))
          )
        + ( (1 - (one / lend zs1))
          * (dist (qbind utail1 (upd zs1 ws1 α1 a1 f1))
                  (qbind utail2 (upd zs2 ws2 α2 a2 f2))
            )
          )
        )
    ?   thm zs1 ws1 a1 f1 zs2 ws2 a2 f2
    ?   relationalunif (tail zs1) (tail zs2)
    ?   relationalpbind ws1 ws2 uhead1
                        (upd zs1 ws1 α1 a1 f1)
                        uhead2
                        (upd zs2 ws2 α2 a2 f2)
                        (relationalupd zs1 ws1 α1 a1 f1 (unif [head zs1]) zs2 ws2 α2 a2 f2 (unif [head zs2]))
    =<= (SGDu.one / (SGDu.lend zs1)) * (dist ws1 ws2) 
        + (1 - (SGDu.one / (SGDu.lend zs1))) 
          * (dist (qbind utail1 (upd zs1 ws1 α1 a1 f1))
                (qbind utail2 (upd zs2 ws2 α2 a2 f2)))
    ?   relationalqbind ws1 ws2 utail1
                        (upd zs1 ws1 α1 a1 f1)
                        utail2
                        (upd zs2 ws2 α2 a2 f2)
    =<= (SGDu.one / (SGDu.lend zs1)) * (dist ws1 ws2) + (1 - (SGDu.one / (SGDu.lend zs1))) * (dist ws1 ws2)
    *** QED
 where
  uhead1 = unif [head zs1]
  utail1 = unif (tail zs1)
  uhead2 = unif [head zs2]
  utail2 = unif (tail zs2)
thm zs1 ws1 _ f1 zs2 ws2 _ f2 = ()

