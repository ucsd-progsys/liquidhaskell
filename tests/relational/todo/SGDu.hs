{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--fast"           @-}

module SGDu where

import           Prelude                 hiding ( head
                                                , tail
                                                , sum
                                                )
import           Data.Functor.Identity
import           Language.Haskell.Liquid.ProofCombinators

{-@ infix : @-}
{-@ type Prob = {v:Double| 0 <= v && v <= 1} @-}
type Prob = Double

{-@ type StepSize = {v:Double | 0.0 <= v } @-}
type StepSize = Double
{-@ data StepSizes = SSEmp | SS StepSize StepSizes @-}
data StepSizes = SSEmp | SS StepSize StepSizes
type DataPoint = (Double, Double)
type Weight = Double
type LossFunction = DataPoint -> Weight -> Double

type Set a = [a]
{-@ type DataSet = {v:Set DataPoint| 0 < len v && 0.0 < lend v } @-}
type DataSet = Set DataPoint
type Distr a = a
type DataDistr = Distr DataPoint

{-@ measure dist :: a -> a -> Double @-}
{-@ assume dist :: x1:_ -> x2:_ -> {v:Double | v == dist x1 x2 } @-}
dist :: a -> a -> Double
dist _ _ = 0

{-@ assume relationalchoice :: p:Prob -> e1:Distr a -> e1':Distr a 
        ->  q:{Prob | p = q } -> e2:Distr a -> e2':Distr a 
        ->  {dist (choice p e1 e1') (choice q e2 e2') <= p * (dist e1 e2) + (1.0 - p) * (dist e1' e2')} @-}
relationalchoice :: Prob -> Distr a -> Distr a -> Prob -> Distr a -> Distr a -> ()
relationalchoice _ _ _ _ _ _ = ()

{-@ measure SGDu.choice :: Prob -> Distr a -> Distr a -> Distr a @-}
{-@ assume choice :: x1:Prob -> x2:Distr a -> x3:Distr a -> {v:Distr a |  v == choice x1 x2 x3 } @-}
choice :: Prob -> Distr a -> Distr a -> Distr a
choice _ x _ = x

{-@ measure SGDu.unif :: zs:DataSet -> DataDistr @-}
{-@ assume unif :: x:DataSet -> {v:DataDistr | v == unif x } @-}
unif :: DataSet -> DataDistr
unif _ = (0,0)

{-@ assume relationalupdatep :: z1:DataPoint -> ws1:Weight -> α1:StepSize -> f1:LossFunction -> 
                          z2:DataPoint -> ws2:Weight -> {α2:StepSize|α1 = α2} -> {f2:LossFunction|f1 = f2} -> 
                            {dist (update z1 ws1 α1 f1) (update z2 ws2 α2 f2) = dist ws1 ws2 + 2.0 * α1} @-}
relationalupdatep ::  DataPoint  -> Weight  -> StepSize  -> LossFunction  -> DataPoint  -> Weight  -> StepSize  -> LossFunction  -> ()
relationalupdatep _ _ _ _ _ _ _ _ = ()

{-@ measure lend @-}
{-@ lend :: xs:[a] -> {v:Double| 0.0 <= v } @-}
lend :: [a] -> Double
lend []       = 0
lend (_ : xs) = 1 + lend xs

{-@ measure SGDu.update :: DataPoint -> Weight -> StepSize -> LossFunction -> Weight @-}
update :: DataPoint -> Weight -> StepSize -> LossFunction -> Weight
update _ w _ _ = w

{-@ reflect one @-}
{-@ one :: {v:Double| v = 1.0 } @-}
one :: Double
one = 1

{-@ assume relationalupdateq :: z1:DataPoint -> ws1:Weight -> α1:StepSize -> f1:LossFunction -> 
                                  {z2:DataPoint|z1 = z2} -> ws2:Weight -> {α2:StepSize|α1 = α2} -> {f2:LossFunction|f1 = f2} -> 
                                    {dist (update z1 ws1 α1 f1) (update z2 ws2 α2 f2) = dist ws1 ws2} @-}
relationalupdateq ::  DataPoint  -> Weight  -> StepSize  -> LossFunction  -> DataPoint  -> Weight  -> StepSize  -> LossFunction  -> ()
relationalupdateq = undefined


{-@ assume relationalpbind :: e1:Distr a -> f1:(a -> Distr b) -> e2:Distr a -> f2:(a -> Distr b) -> 
        { dist (pbind e1 f1) (pbind e2 f2) = dist e1 e2} @-}
relationalpbind :: Distr a  -> (a -> Distr b)  -> Distr a  -> (a -> Distr b) -> ()
relationalpbind = undefined

{-@ assume relationalqbind :: e1:Distr a -> f1:(a -> Distr b) -> {e2:Distr a | e1 = e2} -> f2:(a -> Distr b) -> 
        { dist (qbind e1 f1) (qbind e2 f2) = dist e1 e2} @-}
relationalqbind :: Distr a  -> (a -> Distr b)  -> Distr a  -> (a -> Distr b)  ->  ()
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

{-@ reflect sum @-}
{-@ sum :: StepSizes -> {v:StepSize | 0.0 <= v } @-}
sum :: StepSizes -> Double
sum SSEmp       = 0
sum (SS a as) = a + sum as

{-@ reflect estab @-}
{-@ estab :: DataSet -> StepSizes -> {v:Double | 0.0 <= v} @-}
estab :: DataSet -> StepSizes -> Double
estab zs as = 2.0 / (lend zs) * sum as

{-@ ple estabconsR @-}
{-@ measure SGDu.estabconsR  :: DataSet -> StepSize -> StepSizes -> ()  @-}
{-@ estabconsR :: zs:{DataSet | lend zs /= 0} -> x:StepSize -> xs:StepSizes 
                     -> { estab zs (SS x xs) == 2.0 * x * (one / lend zs) + estab zs xs } @-}
estabconsR :: DataSet -> StepSize -> StepSizes -> () 
estabconsR zs x xs 
  =   estab zs (SS x xs)
  ==. 2.0 / (lend zs) * sum (SS x xs)
  ==. 2.0 * x * (one / lend zs) + estab zs xs 
  *** QED 


{-@ reflect head @-}
{-@ head :: {xs:[a] | len xs > 0 } -> a @-}
head :: [a] -> a
head (z : _) = z

{-@ reflect tail @-}
{-@ tail :: {xs:[a] | len xs > 0 } -> {v:[a] | len v == len xs - 1 && lend v == lend xs - 1 } @-}
tail :: [a] -> [a]
tail (_ : zs) = zs

{-@ measure sslen @-}
sslen :: StepSizes -> Int 
{-@ sslen :: StepSizes -> Nat @-}
sslen SSEmp = 0 
sslen (SS _ ss) = 1 + sslen ss 

{-@ reflect upd @-}
{-@ upd :: zs:{DataSet | 1 < len zs  && 1 < lend zs } -> Weight -> StepSize -> ss:StepSizes -> LossFunction -> DataPoint 
        -> Distr Weight / [ sslen ss, 1 ] @-}
upd ::  DataSet  -> Weight  -> StepSize  -> StepSizes  -> LossFunction  -> DataPoint  -> Distr Weight
upd zs w0 α a f z' = sgd zs (update z' w0 α f) a f

{-@ reflect sgd @-}
{-@ sgd :: zs:{DataSet | 1 < len zs && 1 < lend zs } -> Weight -> ss:StepSizes -> LossFunction 
        -> Distr Weight / [ sslen ss, 0 ] @-}
sgd :: DataSet -> Weight -> StepSizes -> LossFunction -> Distr Weight
sgd _  w0 SSEmp   _ = ppure w0
sgd zs w0 (SS α a) f = choice (one / lend zs)
                             (pbind uhead (upd zs w0 α a f))
                             (qbind utail (upd zs w0 α a f)) `rconst` estabconsR zs α a
 where
  uhead = unif [head zs]
  utail = unif (tail zs)


{-@ reflect rconst @-}
rconst :: a -> b -> a 
rconst x _ = x 

{-@ ple thm @-}
{-@ thm :: zs1:{DataSet | 1 < lend zs1 && 1 < len zs1 } -> ws1:Weight -> α1:StepSizes -> f1:LossFunction -> 
           zs2:{DataSet | 1 < lend zs2 && 1 < len zs2 && lend zs1 == lend zs2 && tail zs1 = tail zs2} -> 
            ws2:Weight -> {α2:StepSizes| α2 = α1} -> {f2:LossFunction|f1 = f2} -> 
            {dist (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2) <= dist ws1 ws2 + estab zs1 α1} @-}
thm :: DataSet  -> Weight  -> StepSizes  -> LossFunction  -> DataSet  -> Weight  -> StepSizes  -> LossFunction  -> ()
thm zs1 ws1 α1@SSEmp f1 zs2 ws2 α2@SSEmp f2 =
  dist (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2)
    =<= dist (ppure ws1) (ppure ws2) + estab zs1 α1
    *** QED 

thm zs1 ws1 as1@(SS α1 a1) f1 zs2 ws2 as2@(SS α2 a2) f2 =
  dist (sgd zs1 ws1 as1 f1) (sgd zs2 ws2 as2 f2)
    === dist
          (choice (one / lend zs1) (pbind uhead1 updWs1) (qbind utail1 updWs1) `rconst` estabconsR zs1 α1 a1)
          (choice (one / lend zs2) (pbind uhead2 updWs2) (qbind utail2 updWs2) `rconst` estabconsR zs2 α2 a2)
    === dist
          (choice (one / lend zs1) (pbind uhead1 updWs1) (qbind utail1 updWs1))
          (choice (one / lend zs2) (pbind uhead2 updWs2) (qbind utail2 updWs2))
    ?   relationalchoice (one / lend zs1) (pbind uhead1 updWs1) (qbind utail1 updWs1)
                         (one / lend zs2) (pbind uhead2 updWs2) (qbind utail2 updWs2)

    === (one / lend zs1) * (dist (pbind uhead1 updWs1) (pbind uhead2 updWs2)) 
        + (1 - (one / lend zs1)) * (dist (qbind utail1 updWs1) (qbind utail2 updWs2))
        ?   relationalpbind uhead1 updWs1 uhead2 updWs2 

    === (one / lend zs1) * (dist (updWs1 uhead1) (updWs2 uhead2)) 
        + (1 - (one / lend zs1)) * (dist (qbind utail1 updWs1) (qbind utail2 updWs2))
        ?   thm zs1 (update uhead1 ws1 α1 f1) a1 f1 zs2 (update uhead2 ws2 α2 f2) a2 f2

    === (one / lend zs1) * (dist (update uhead1 ws1 α1 f1) (update uhead2 ws2 α2 f2) + estab zs1 a1) 
        + (1 - (one / lend zs1)) * (dist (qbind utail1 updWs1) (qbind utail2 updWs2))    
        ?   relationalupdatep uhead1 ws1 α1 f1 uhead2 ws2 α2 f2
   
    === (one / lend zs1) * (dist ws1 ws2 + 2 * α1 + estab zs1 a1) 
          + (1 - (one / lend zs1)) * (dist (qbind utail1 updWs1) (qbind utail2 updWs2))         
        ?   relationalqbind utail1 updWs1 utail2 updWs2 

    === (one / lend zs1) * (dist ws1 ws2 + 2 * α1 + estab zs1 a1) 
          + (1 - (one / lend zs1)) * (dist (updWs1 utail1) (updWs2 utail2))         
        ?   thm zs1 (update utail1 ws1 α1 f1) a1 f1 zs2 (update utail2 ws2 α2 f2) a2 f2
        ?   relationalupdateq utail1 ws1 α1 f1 utail2 ws2 α2 f2

    === (one / lend zs1) * (dist ws1 ws2 + 2 * α1 + estab zs1 a1) 
          + (1 - (one / lend zs1)) * (dist ws1 ws2 + estab zs1 a1)

    === dist ws1 ws2 + 2.0 * α1 * (one / lend zs1) + estab zs1 a1
        ? estabconsR zs1 α1 a1
                            
    === dist ws1 ws2 + estab zs1 (SS α1 a1)
    === dist ws1 ws2 + estab zs1 as1
    *** QED 
 where
  updWs1 = upd zs1 ws1 α1 a1 f1
  updWs2 = upd zs2 ws2 α2 a2 f2
  uhead1 = unif [head zs1]
  utail1 = unif (tail zs1)
  uhead2 = unif [head zs2]
  utail2 = unif (tail zs2)
thm zs1 ws1 _ f1 zs2 ws2 _ f2 = ()