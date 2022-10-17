module SGD where

import           Prelude                 hiding ( elem
                                                , sum
                                                )
import           Data.Functor.Identity

{-@ type Prob = {v:Double|0 <= v && v <= 1} @-}
type Prob = Double
-- {-@ type StepSize = {v:Double|0 <= v} @-}
type StepSize = Double
type DataPoint = (Double, Double)
type Weight = Double
type LossFunction = DataPoint -> [Weight] -> Double

type Set a = [a]
type DataSet = Set DataPoint

{- Cu(e,x.φ) ≜ ∃n,y. (e 􏰁 {cstepn(cret(y))}) ∧ φ[y/x] -}

{- Cid :: {v:Distr a | φ (runIdentity v) } -}

-- {-@ relational Distr a ~ Distr b ~~ x1 = x2 => r1  @-}
type Distr a = Identity a
type DataDistr = Distr DataPoint

{-@ reflect one @-}
{-@ one :: {v:Double|v = 1} @-}
one :: Double
one = 1

{-@ reflect diff @-}
{-@ diff :: xs:[a] -> ys:{[a]|lend ys == lend xs} -> {v:Double|0 <= v} @-}
diff :: Eq a => [a] -> [a] -> Double
diff (x : xs) (y : ys) | x == y = diff xs ys
diff (x : xs) (y : ys) | x /= y = 1 + diff xs ys
diff _ _                        = 0

{-@ measure dist :: a -> a -> Double @-}
dist :: a -> a -> Double
dist _ _ = 0

{-@ measure SGD.unif :: zs:DataSet -> DataDistr @-}
{-@ reflect unif @-}
{-@ unif :: DataSet -> DataDistr @-}
unif :: DataSet -> DataDistr
unif zs = ppure (if null zs then (0, 0) else head zs)


data Foo = Foo
type Arg a = Foo -> a

{-@ measure SGD.choice :: Prob -> Distr a -> Distr a -> Distr a @-}
{-@ choice :: (Prob) -> Distr a -> Distr a -> Distr a @-}
choice :: (Double) -> Distr a -> Distr a -> Distr a
choice p a b = a

{-@ measure SGD.l :: Double @-}
{-@ measure SGD.l' :: Double @-}

update :: DataPoint -> [Weight] -> StepSize -> LossFunction -> [Weight]
update z w α f = w

{-@ sgd :: DataSet -> [Weight] -> [StepSize] -> LossFunction -> Distr [Weight] @-}
sgd :: DataSet -> [Weight] -> [StepSize] -> LossFunction -> Distr [Weight]
sgd zs w0 []      f = pure w0
sgd zs w0 (α : a) f = do
  z' <- unif zs
  sgd zs (update z' w0 α f) a f
{-
    === let z' = choice (1 / length zs) (unif [z]) (unif zs0) in 
            let w'= update z' w0 α f in 
                sgd zs w' a f
        ? Unif (zs0 ++ [z]) = Choice |S|/|S++S'| Unif(S) Unif(S')
    === choice (1 / length zs) 
            (let z' = unif [z] in sgd zs (update z' w0 α f) a f) 
            (let z' = unif zs0 in sgd zs (update z' w0 α f) a f)
        ? let z = choice p mu mu' in e === choice p (let z = mu in e) (let z = mu' in e)
-}

-- {-@ unif ~ unif :: zs1:DataSet -> DataDistr
--                  ~ zs2:DataSet -> DataDistr
--                 ~~ zs1 = zs2 && @-}


{-@ measure SGD.ppure :: a -> Distr a @-}

ppure :: a -> Distr a
ppure = undefined

{-@ assume relational ppure ~ ppure :: x1:a -> Distr a 
                                     ~ x2:a -> Distr a 
                                    ~~ true => dist (r1 x1) (r2 x2) <= dist x1 x2 @-}

{-
      x1 ~ x2 => s1 ~ s2 | Phi  
     --------------------------------------- unit
      pure x1 ~ pure x2 => m s1 ~ m s2 | 
      
-}

pbind :: Distr a -> (a -> Distr b) -> Distr b
pbind = undefined

qbind :: Distr a -> (a -> Distr b) -> Distr b
qbind = undefined

{-  


-}

-- TODO: add ws1 ws2
{-@ assume relational pbind ~ pbind :: μ1:Distr a -> f1:(y1:a -> Distr b) -> Distr b 
                                     ~ μ2:Distr a -> f2:(y2:a -> Distr b) -> Distr b
                                    ~~ true =>
                                        true => 
                                            dist (r1 μ1 f1) (r2 μ2 f2) <= SGD.l @-}

{- {()|true => true => (forall x1 x2. x1 /= x2 => dist (f1 x1) (f2 x2) <= SGD.l) => dist (r1 μ1 f1) (r2 μ2 f2) <= SGD.l} -}

{- f :: (x1 = x2 => dist (f1 x1) (f2 x2) <= SGD.l) -}

{- f ~ g | -}
{- pbind ~ pbind | p[μ1 := a][f1 := f][μ2 := b][f2 := g] -}
{- pbind a f ~ pbind b g | theorem -}

{-@ assume relational qbind ~ qbind :: μ1:Distr a -> f1:(y1:a -> Distr b) -> Distr b
                                     ~ μ2:Distr a -> f2:(y2:a -> Distr b) -> Distr b
                                    ~~ μ1 = μ2 => true => dist (r1 μ1 f1) (r2 μ2 f2) <= SGD.l' @-}

{- 
forall μ1 μ2 f1 f2. μ1 = μ2 => (forall x1 x2. x1 = x2 => dist (f1 x1) (f2 x2) <= SGD.l') => dist (r1 μ1 f1) (r2 μ2 f2) <= SGD.l'
forall μ1 μ2 x1 x1 f1 f2. μ1 = μ2 => true => (x1 = x2 => dist (f1 x1) (f2 x2) <= SGD.l') => dist (r1 μ1 f1) (r2 μ2 f2) <= SGD.l'
-}

-- {-@ unif zs0 >>= \z' -> sgd zs1 (update z' w1 α f) a f ~ unif zs0 >>= \z' -> sgd zs2 (update z' w2 α f) a f
--     :: Distr [Weight] ~ Distr [Weight] ~~ @-}



{- 
                 a1 ~ a2 | g
                 g <: <> Phi r1 r2
                 a1 ~ a2 | <> Phi r1 r2
f1 ~ f2 | forall x1 x2. Phi x1 x2 => <> Psi (r1 x1) (r2 x2)
f1 ~ f2 | p => q
p => q <: forall x1 x2. Phi x1 x2 => <> Psi (r1 x1) (r2 x2)
---------------------------------------------------------------bind
             bind a1 f1 ~ bind a2 f2 | <> Psi
-}

{- {<> Phi} forall a1 a2, <> Phi a1 a2 -> <> Psi (f1 a1) (f2 a2) -> <> Psi (bind a1 f1) (bind a2 f2)
                                
        a1 ~ a2 => m s1 ~ m s2 | Phi (runId r1) (runId r2)
        f1 ~ f2 => x1:s1 -> m t1 ~ x2:s2 -> m t2 | Phi x1 x2 => Psi
     ----------------------------------------------------------------------------------------- bind
        bind a1 f1 ~ bind a2 f2 => m t1 ~ m t2 | Psi
-}
-- ||w_i - w'_i|| + 2Lα_i  = ||w_i-1 - w'_i-1|| + 2Lα_i + 2Lα_i_1 = ...
-- ||w_i - w'_i|| = ||w_i-1 - w'_i-1|| + 2Lα_i-1 = ...
{-@ assume relational choice ~ choice 
        :: p:Prob -> e1:Distr a -> e1':Distr a -> Distr a
            ~ q:Prob -> e2:Distr a -> e2':Distr a -> Distr a
            ~~ p = q => true =>                
                true =>                        
                    dist (r1 p e1 e1') (r2 q e2 e2') <= p * dist e1 e2 + (1 - p) * dist e1' e2' @-}             -- ||w_0 - w'_0|| + 2pLα * len a_i
            -- p * (p * dist e1_(i-1) e2_(i-1) + (1 - p) * dist e1' e2') + (1 - p) * (p * dist e1 e2 + (1 - p) * dist e1' e2')

{-@ relational sgd' ~ sgd' :: zs1:DataSet -> ws1:[Weight] -> α1:[StepSize] -> f1:LossFunction -> Distr [Weight] 
                            ~ zs2:DataSet -> ws2:[Weight] -> α2:[StepSize] -> f2:LossFunction -> Distr [Weight]
                           ~~ 1 = SGD.lend zs1 && SGD.lend zs1 = SGD.lend zs2 => 
                                true =>
                                    SGD.lend α1 = SGD.lend α2 => f1 = f2 =>
                                        dist (r1 zs1 ws1 α1 f1) (r2 zs2 ws2 α2 f2) 
                                            <= (SGD.one / SGD.lend zs1) * dist ws1 ws2 + (1 - (SGD.one / SGD.lend zs1)) * dist ws1 ws2 @-}


{- dist r1 r2 <= (one / lend zs1) * SGD.l + (1 - one / lend zs1) * SGD.l' -}
{-@ sgd' :: {v:DataSet|len v > 0} -> [Weight] -> [StepSize] -> LossFunction -> Distr [Weight] @-}
sgd' :: DataSet -> [Weight] -> [StepSize] -> LossFunction -> Distr [Weight]
sgd' _  w0 []      _ = ppure w0
sgd' zs w0 (α : a) f = choice (one / lend zs)
                              (pbind uhead upd)
                              (qbind utail upd)
 where
  uhead = unif [head zs]
  utail = unif (tail zs)
  upd z' = sgd' zs (update z' w0 α f) a f

{-@ assume (/) :: x:_ -> y:_ -> {v:_|v = x / y} @-}

{- 
{-@ foo :: {v:[Prob]|SGD.lend v >= 1} -> DataSet -> DataSet -> Distr DataPoint @-}
foo :: [Double] -> DataSet -> DataSet -> Distr DataPoint
foo zs x y = choice (one / lend zs) (unif x) (unif y)

{-@ relational foo ~ foo :: z1:_ -> x1:_ -> y1:_ -> _ ~ z2:_ -> x2:_ -> y2:_ -> _
              ~~ SGD.lend z1 >= 1 && SGD.lend z1 = SGD.lend z2 => 
                    dist (SGD.unif x1) (SGD.unif x2) <= SGD.l => dist (SGD.unif y1) (SGD.unif y2) <= SGD.l' => 
                        dist (r1 x1 y1) (r2 x2 y2) <= (SGD.one / SGD.lend z1) * SGD.l + (1 - SGD.one / SGD.lend z1) * SGD.l'
@-}
-}

{-
z1  := head zs1
z2  := head zs2
zs0 := tail zs2 = tail zs2

choice (1 / length zs1) 
            (unif [z1] >>= \z' -> sgd zs1 (update z' w1 α f) a f)
            (unif zs0 >>= \z' -> sgd zs1 (update z' w1 α f) a f)
    ~ choice (1 / length zs2) 
            (unif [z2] >>= \z' -> sgd zs2 (update z' w2 α f) a f)
            (unif zs0 >>= \z' -> sgd zs2 (update z' w2 α f) a f)
        | dist (r1 zs1 w1 α f) (r2 zs2 w2 α f) <= dist w1 w2 + (1 / length zs1) * 2 * L * (sum α)

I. choice ~ choice :: p1:Prob -> e1:Distr a -> e1':Distr a -> Distr a
                    ~ p2:Prob -> e2:Distr a -> e2':Distr a -> Distr a
                    | p1 = p2 =>                                         
                        dist e1 e2 <= k =>                               
                            dist e1' e2' <= k' =>
                                dist r1 r2 <= p * k + (1 - p) * k'
1 - p := 1 / length zs1
k     := dist w1 w2 + 2 * L * sum (α:a)
k'    := dist w1 w2 

II. z' = unif [z]

z1' ~ z2' | true

sgd zs1 (update z1' w1 α f) a f 
    ~ sgd zs2 (update z2' w2 α f) a f 
        | dist r1 r2 <= dist (update z1' w1 α f) (update z2' w2 α f) + (1 / length zs1) * 2 * L * sum a

sgd zs1 (update z1' w1 α f) a f 
    ~ sgd zs2 (update z2' w2 α f) a f 
        | dist r1 r2 <= dist w1 w2 + 2 * L * α + (1 / length zs1) * 2 * L * sum a

sgd zs1 (update z1' w1 α f) a f 
    ~ sgd zs2 (update z2' w2 α f) a f 
        | dist r1 r2 <= dist w1 w2 + 2 * L * sum (α:a)

QED.

III. z' = unif zs0

sgd zs1 (update z1' w1 α f) a f 
    ~ sgd zs2 (update z2' w2 α f) a f 
        | dist r1 r2 <= dist (update z1' w1 α f) (update z2' w2 α f) + (1 / length zs1) * 2 * L * sum a

sgd zs1 (update z1' w1 α f) a f 
    ~ sgd zs2 (update z2' w2 α f) a f 
        | dist r1 r2 <= k

QED.
-}

{-@ measure lend @-}
{-@ lend :: xs:[a] -> {v:Double|v >= 0 && (1 <= v <=> 1 <= len xs)} @-}
lend :: [a] -> Double
lend []       = 0
lend (_ : xs) = 1 + lend xs

{-@ reflect disjunion @-}
disjunion :: [DataPoint] -> [DataPoint] -> [DataPoint]
disjunion [] ys                   = ys
disjunion (x : xs) ys | elem x ys = disjunion xs ys
disjunion (x : xs) ys             = x : disjunion xs ys

-- {-@ inline axiom @-}
-- axiom :: [DataPoint] -> [DataPoint] -> Bool
-- axiom zs zs' = unif (disjunion zs zs') == choice (lend zs / lend (disjunion zs zs')) (unif zs) (unif zs')

-- axiom' zs1 zs2 = unif zs1 == choice (lend (intersect zs1 zs2) / lend zs1) (intersect zs1 zs2) (minus zs1 zs2)
-- axiom'' = let z = choice p mu mu' in e ~> choice p (let z = mu in e) (let z = mu' in e)

{-@ reflect elem @-}
elem :: DataPoint -> DataSet -> Bool
elem _ []       = False
elem y (x : xs) = y == x || elem y xs

{-@ reflect intersect @-}
{-@ intersect :: zs1:DataSet -> zs2:DataSet -> {v:DataSet|lend v <= lend zs1} @-}
intersect :: DataSet -> DataSet -> DataSet
intersect [] _                    = []
intersect (x : xs) ys | elem x ys = x : intersect xs ys
intersect (_ : xs) ys             = intersect xs ys

{-@ reflect minus @-}
minus :: DataSet -> DataSet -> DataSet
minus [] ys                   = []
minus (x : xs) ys | elem x ys = minus xs ys
minus (x : xs) ys             = x : minus xs ys

{-@ reflect sum @-}
sum :: [StepSize] -> StepSize
sum []       = 0
sum (α : αs) = α + sum αs

{-@ reflect div @-}
{-@ div :: Double -> {v:Double|v /= 0} -> Double @-}
div :: Double -> Double -> Double
div a b = a / b

type Sgd
  = DataSet -> Distr [Weight] -> [StepSize] -> LossFunction -> Distr [Weight]

-- {-@ pred :: {zs1:DataSet|lend zs1 /= 0} -> {zs2:DataSet|lend zs1 = lend zs2} -> Sgd -> Sgd -> Distr [Weight] -> Distr [Weight] -> 
--                 [StepSize] -> [StepSize] -> LossFunction -> LossFunction -> Bool @-}
-- pred :: DataSet -> DataSet -> Sgd -> Sgd -> Distr [Weight] -> Distr [Weight] -> [StepSize] -> [StepSize] -> LossFunction -> LossFunction -> Bool
-- pred zs1 zs2 r1 r2 ws1 ws2 α1 α2 f1 f2 = 
--     SGD.unif zs1 == SGD.choice (SGD.lend (SGD.intersect zs1 zs2) / SGD.lend zs1) 
--                                 (SGD.unif (SGD.intersect zs1 zs2)) (SGD.unif (SGD.minus zs1 zs2)) &&
--         SGD.unif zs2 == SGD.choice (SGD.lend (SGD.intersect zs2 zs1) / SGD.lend zs2) 
--                                     (SGD.unif (SGD.intersect zs2 zs1)) (SGD.unif (SGD.minus zs2 zs1)) &&
--             length zs1 == length zs2 && 
--                 dist (r1 zs1 ws1 α1 f1) (r2 zs2 ws2 α2 f2) <= dist ws1 ws2 + 2.0 * SGD.diff zs1 zs2

-- {-@ pred' :: {zs1:DataSet|lend zs1 /= 0} -> {zs2:DataSet|lend zs1 = lend zs2} -> Sgd -> Sgd -> Distr [Weight] -> Distr [Weight] -> 
--                 [StepSize] -> [StepSize] -> LossFunction -> LossFunction -> Bool @-}
-- pred' :: DataSet -> DataSet -> Sgd -> Sgd -> Distr [Weight] -> Distr [Weight] -> [StepSize] -> [StepSize] -> LossFunction -> LossFunction -> Bool
-- pred' zs1 zs2 r1 r2 ws1 ws2 α1 α2 f1 f2 = 
--     SGD.unif zs1 == SGD.choice (SGD.lend (SGD.intersect zs1 zs2) / SGD.lend zs1) 
--                                 (SGD.unif (SGD.intersect zs1 zs2)) (SGD.unif (SGD.minus zs1 zs2)) &&
--         SGD.unif zs2 == SGD.choice (SGD.lend (SGD.intersect zs2 zs1) / SGD.lend zs2) 
--                                     (SGD.unif (SGD.intersect zs2 zs1)) (SGD.unif (SGD.minus zs2 zs1)) &&
--             length zs1 == length zs2 && 
--                 dist (r1 zs1 ws1 α1 f1) (r2 zs2 ws2 α2 f2) <= dist ws1 ws2 + 2.0 * SGD.diff zs1 zs2

-- {-@ relational sgd ~ sgd :: zs1:DataSet -> ws1:Distr [Weight] -> α1:[StepSize] -> f1:LossFunction -> v:Distr [Weight] 
--                           ~ zs2:DataSet -> ws2:Distr [Weight] -> α2:[StepSize] -> f2:LossFunction -> v:Distr [Weight]
--                          ~~ SGD.unif zs1 = SGD.choice (SGD.lend (SGD.intersect zs1 zs2) / SGD.lend zs1) 
--                                                         (SGD.unif (SGD.intersect zs1 zs2)) (SGD.unif (SGD.minus zs1 zs2)) &&
--                                 SGD.unif zs2 = SGD.choice (SGD.lend (SGD.intersect zs2 zs1) / SGD.lend zs2) 
--                                                             (SGD.unif (SGD.intersect zs2 zs1)) (SGD.unif (SGD.minus zs2 zs1)) |- 
--                                     SGD.lend zs1 /= 0 && SGD.lend zs1 = SGD.lend zs2 => true => α1 = α2 => f1 = f2 => 
--                                         dist (r1 zs1 ws1 α1 f1) (r2 zs2 ws2 α2 f2) <= 
--                                             dist ws1 ws2 + 2.0 * (1 - (SGD.lend (SGD.intersect zs1 zs2) / SGD.lend zs1)) * SGD.sum α1 @-}

-- {-@ relational sgd' ~ sgd' :: zs1:DataSet -> ws1:[Weight] -> α1:[StepSize] -> f1:LossFunction -> Distr [Weight] 
--                             ~ zs2:DataSet -> ws2:[Weight] -> α2:[StepSize] -> f2:LossFunction -> Distr [Weight]
--                            ~~ SGD.intersect zs1 zs2 = tail zs1 && SGD.intersect zs1 zs2 = tail zs2 && 
--                                     SGD.minus zs1 zs2 = [head zs1] && SGD.minus zs2 zs1 = [head zs2] => 
--                                         dist ws1 ws2 <= (SGD.one / SGD.lend zs1) * SGD.l + 
--                                                             (1 - SGD.one / SGD.lend zs1) * SGD.l' =>
--                                             α1 = α2 => f1 = f2 => 
--                                                 dist (r1 zs1 ws1 α1 f1) (r2 zs2 ws2 α2 f2) 
--                                                     <= (SGD.one / SGD.lend zs1) * SGD.l + 
--                                                             (1 - SGD.one / SGD.lend zs1) * SGD.l' @-}

{-@ relational sgd' ~ sgd' :: zs1:DataSet -> ws1:[Weight] -> α1:[StepSize] -> f1:LossFunction -> Distr [Weight] 
                            ~ zs2:DataSet -> ws2:[Weight] -> α2:[StepSize] -> f2:LossFunction -> Distr [Weight]
                           ~~ 1 = SGD.lend zs1 && SGD.lend zs1 = SGD.lend zs2 => 
                                dist ws1 ws2 <= SGD.l + SGD.l' =>
                                    true => true =>
                                        dist (r1 zs1 ws1 α1 f1) (r2 zs2 ws2 α2 f2) 
                                            <= (SGD.one / SGD.lend zs1) * SGD.l + (1 - SGD.one / SGD.lend zs1) * SGD.l' @-}

-- {-@ (>>=) w1 update ~ (>>=) w2 update | p @-}
-- {-@ update ~ update | k @-}

-- {-@ update ~ update | k @-}

{-@ assume relational update ~ update :: z1:DataPoint -> ws1:[Weight] -> α1:StepSize -> f1:LossFunction -> [Weight]
                                       ~ z2:DataPoint -> ws2:[Weight] -> α2:StepSize -> f2:LossFunction -> [Weight] 
                                      ~~ z1 = z2 => true => α1 = α2 => f1 = f2 => 
                                            dist (r1 z1 ws1 α1 f1) (r2 z2 ws2 α2 f2) <= SGD.l' @-}

{-@ assume relational update ~ update :: z1:DataPoint -> ws1:[Weight] -> α1:StepSize -> f1:LossFunction -> [Weight]
                                       ~ z2:DataPoint -> ws2:[Weight] -> α2:StepSize -> f2:LossFunction -> [Weight] 
                                      ~~ true => true => α1 = α2 => f1 = f2 => 
                                            dist (r1 z1 ws1 α1 f1) (r2 z2 ws2 α2 f2) <= SGD.l @-}
