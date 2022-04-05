{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--fast"           @-}
{-@ LIQUID "--ple"            @-}


module SGDu where

import           Prelude                 hiding ( head
                                                , tail
                                                , sum
                                                )
import           Data.Functor.Identity
import           Language.Haskell.Liquid.ProofCombinators

{-@ infix : @-}
type Prob = Double

type StepSize = Double
data StepSizes = SSEmp | SS StepSize StepSizes
type DataPoint = (Double, Double)
type Weight = Double
type LossFunction = DataPoint -> Weight -> Double

type Set a = [a]
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

{-@ assume relational choice ~ choice 
        :: p:_ -> e1:_ -> e1':_ -> _
         ~ q:_ -> e2:_ -> e2':_ -> _
        ~~ p = q => true => true => 
            dist (r1 p e1 e1') (r2 q e2 e2') <= p * (dist e1 e2) + (1.0 - p) * (dist e1' e2') @-}



{-@ measure SGDu.choice :: Prob -> Distr a -> Distr a -> Distr a @-}
{-@ choice :: x1:Prob -> x2:Distr a -> x3:Distr a -> {v:Distr a |  v == choice x1 x2 x3 } @-}
choice :: Prob -> Distr a -> Distr a -> Distr a
choice _ x _ = x

{-@ measure SGDu.unif :: zs:DataSet -> DataDistr @-}
{-@ assume unif :: x:DataSet -> {v:DataDistr | v == unif x } @-}
unif :: DataSet -> DataDistr
unif _ = (0,0)

{-@ assume relationalupdatep :: z1:DataPoint -> ws1:Weight -> α1:StepSize -> f1:LossFunction -> 
                          z2:DataPoint -> ws2:Weight -> {α2:StepSize|α1 = α2} -> {f2:LossFunction|f1 = f2} -> 
                            {dist (update z1 ws1 α1 f1) (update z2 ws2 α2 f2) = dist ws1 ws2} @-}
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
                                  {z2:DataPoint| true} -> ws2:Weight -> {α2:StepSize|α1 = α2} -> {f2:LossFunction|f1 = f2} -> 
                                    {dist (update z1 ws1 α1 f1) (update z2 ws2 α2 f2) = dist ws1 ws2} @-}
relationalupdateq ::  DataPoint  -> Weight  -> StepSize  -> LossFunction  -> DataPoint  -> Weight  -> StepSize  -> LossFunction  -> ()
relationalupdateq = undefined

{-@ assume relational update ~ update 
      :: z1:_ -> ws1:_ -> α1:_ -> f1:_ -> _ 
       ~ z2:_ -> ws2:_ -> α2:_ -> f2:_ -> _
      ~~ true => true => α1 = α2 => f1 = f2 => 
          dist (r1 z1 ws1 α1 f1) (r2 z2 ws2 α2 f2) = dist ws1 ws2 @-}

{-@ assume relational pbind ~ pbind :: e1:_ -> f1:_ -> _
                                     ~ e2:_ -> f2:_ -> _
                                    ~~ true => true => 
                                          dist (r1 e1 f1) (r2 e2 f2) = dist (f1 e1) (f2 e2) @-}


{-@ assume relational qbind ~ qbind :: e1:_ -> f1:_ -> _
                                     ~ e2:_ -> f2:_ -> _
                                    ~~ true => true => 
                                          dist (r1 e1 f1) (r2 e2 f2) = dist (f1 e1) (f2 e2) @-}

{-@ assume relationalpbind :: e1:Distr a -> f1:(a -> Distr b) -> e2:Distr a -> f2:(a -> Distr b) -> 
        { dist (pbind e1 f1) (pbind e2 f2) = dist (f1 e1) (f2 e2)} @-}
relationalpbind :: Distr a  -> (a -> Distr b)  -> Distr a  -> (a -> Distr b) -> ()
relationalpbind = undefined


{-@ assume relationalqbind :: e1:Distr a -> f1:(a -> Distr b) -> {e2:Distr a | e1 = e2} -> f2:(a -> Distr b) -> 
        { dist (qbind e1 f1) (qbind e2 f2) = dist (f1 e1) (f2 e2)} @-}
relationalqbind :: Distr a  -> (a -> Distr b)  -> Distr a  -> (a -> Distr b)  ->  ()
relationalqbind = undefined

{-@ measure SGDu.pbind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ pbind :: x1:Distr a -> x2:(a -> Distr b) 
          -> {v:Distr b | v = SGDu.pbind x1 x2 } @-}
pbind :: Distr a -> (a -> Distr b) -> Distr b
pbind a f = const (f a) ()  -- f a
{-# NOINLINE pbind #-}

{-@ measure SGDu.qbind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ qbind :: x1:Distr a -> x2:(a -> Distr b) 
          -> {v:Distr b | v = SGDu.qbind x1 x2 } @-}
qbind :: Distr a -> (a -> Distr b) -> Distr b
qbind x f = f x 

{-@ reflect ppure @-}
ppure :: a -> Distr a
ppure x = x

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
{-@ sgd :: zs:{DataSet | 1 < len zs && 1 < lend zs } -> Weight -> ss:StepSizes -> _ 
        -> Distr Weight / [ sslen ss, 0 ] @-}
sgd :: DataSet -> Weight -> StepSizes -> LossFunction -> Distr Weight
sgd _  w0 SSEmp   _ = ppure w0
sgd zs w0 (SS α a) f = thm zs w0 a f zs w0 a f `cast` 
                          choice (one / lend zs)
                             (pbind uhead (upd zs w0 α a f))
                             (qbind utail (upd zs w0 α a f)) 
                        
 where
  uhead = unif [head zs]
  utail = unif (tail zs)


{-@ reflect rconst @-}
rconst :: a -> b -> a 
rconst x _ = x 

{-@ relational sgd ~ sgd :: zs1:{_ | 1 < len zs1 && 1 < lend zs1 } -> ws1:_ -> α1:_ -> f1:_ -> _ 
                         ~  zs2:{_ | 1 < len zs2 && 1 < lend zs2 } -> ws2:_ -> α2:_ -> f2:_ -> _
                         ~~ (1 < SGDu.lend zs1 && 1 < len zs1 && 1 < SGDu.lend zs2 && 1 < len zs2 && SGDu.lend zs1 == SGDu.lend zs2 && tail zs1 = tail zs2)
                                => true => α2 = α1 => f1 = f2 => true 
                                @-}


{-@ ple thm @-}
{-@ thm :: zs1:{DataSet | 1 < lend zs1 && 1 < len zs1 } -> ws1:Weight -> α1:StepSizes -> f1:LossFunction -> 
           zs2:{DataSet | 1 < lend zs2 && 1 < len zs2 && lend zs1 == lend zs2 && tail zs1 = tail zs2} -> 
            ws2:Weight -> {α2:StepSizes| α2 = α1} -> {f2:LossFunction|f1 = f2} -> 
            {dist (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2) <= dist ws1 ws2} @-}
thm :: DataSet  -> Weight  -> StepSizes  -> LossFunction  -> DataSet  -> Weight  -> StepSizes  -> LossFunction  -> ()
thm zs1 ws1 α1@SSEmp f1 zs2 ws2 α2@SSEmp f2
  =  dist (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2)
  =<= dist (ppure ws1) (ppure ws2)
  *** QED 

thm zs1 ws1 as1@(SS α1 a1) f1 zs2 ws2 as2@(SS α2 a2) f2 =
  dist (sgd zs1 ws1 as1 f1) (sgd zs2 ws2 as2 f2)
   ==. dist (thm zs1 ws1 a1 f1 zs1 ws1 a1 f1 `cast` sgd zs1 ws1 as1 f1) 
        (thm zs2 ws2 a2 f2 zs2 ws2 a2 f2 `cast` sgd zs2 ws2 as2 f2)
   ==. dist
          (choice (one / lend zs1) (pbind uhead1 updWs1) (qbind utail1 updWs1))
          (choice (one / lend zs2) (pbind uhead2 updWs2) (qbind utail2 updWs2))
    ?   relationalchoice (one / lend zs1) (pbind uhead1 updWs1) (qbind utail1 updWs1)
                         (one / lend zs2) (pbind uhead2 updWs2) (qbind utail2 updWs2)

    ==. (one / lend zs1) * (dist (pbind uhead1 updWs1) (pbind uhead2 updWs2)) 
        + (1 - (one / lend zs1)) * (dist (qbind utail1 updWs1) (qbind utail2 updWs2))
        ?   relationalpbind uhead1 updWs1 uhead2 updWs2 

    ==. (one / lend zs1) * (dist (updWs1 uhead1) (updWs2 uhead2)) 
        + (1 - (one / lend zs1)) * (dist (qbind utail1 updWs1) (qbind utail2 updWs2))
        ?   thm zs1 (update uhead1 ws1 α1 f1) a1 f1 zs2 (update uhead2 ws2 α2 f2) a2 f2

    ==. (one / lend zs1) * (dist (update uhead1 ws1 α1 f1) (update uhead2 ws2 α2 f2)) 
        + (1 - (one / lend zs1)) * (dist (qbind utail1 updWs1) (qbind utail2 updWs2))    
        ?   (dist (update uhead1 ws1 α1 f1) (update uhead2 ws2 α2 f2)
                  ? relationalupdatep uhead1 ws1 α1 f1 uhead2 ws2 α2 f2
              === dist ws1 ws2
              *** QED)
   
    ==. (one / lend zs1) * (dist ws1 ws2) 
          + (1 - (one / lend zs1)) * (dist (qbind utail1 updWs1) (qbind utail2 updWs2))         
        ?   relationalqbind utail1 updWs1 utail2 updWs2 

    ==. (one / lend zs1) * (dist ws1 ws2) 
          + (1 - (one / lend zs1)) * (dist (updWs1 utail1) (updWs2 utail2))         
        ?   thm zs1 (update utail1 ws1 α1 f1) a1 f1 zs2 (update utail2 ws2 α2 f2) a2 f2
        ?   relationalupdateq utail1 ws1 α1 f1 utail2 ws2 α2 f2

    ==. (one / lend zs1) * (dist ws1 ws2) 
          + (1 - (one / lend zs1)) * (dist ws1 ws2)

    ==. dist ws1 ws2
    *** QED 
 where
  updWs1 = upd zs1 ws1 α1 a1 f1
  updWs2 = upd zs2 ws2 α2 a2 f2
  uhead1 = unif [head zs1]
  utail1 = unif (tail zs1)
  uhead2 = unif [head zs2]
  utail2 = unif (tail zs2)
thm zs1 ws1 _ f1 zs2 ws2 _ f2 = ()