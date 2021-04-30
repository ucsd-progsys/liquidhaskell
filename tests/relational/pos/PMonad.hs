module PMonad where

import           Prelude                 hiding ( elem
                                                , sum
                                                )
import           Data.Functor.Identity

type Distr a = Identity a

{-@ measure PMonad.l :: Double @-}

{-@ measure dist :: a -> a -> Double @-}
dist :: a -> a -> Double
dist = undefined

ppure :: a -> Distr a
ppure = undefined

{-@ assume relational ppure ~ ppure :: x1:a -> Distr a
                                     ~ x2:a -> Distr a 
                                    ~~ dist x1 x2 <= PMonad.l => dist (r1 x1) (r2 x2) <= PMonad.l @-}

pbind :: Distr a -> (a -> Distr b) -> Distr b
pbind = undefined

{-@ assume relational pbind ~ pbind :: μ1:Distr a -> f1:(x1:a -> Distr b) -> Distr b 
                                     ~ μ2:Distr a -> f2:(x2:a -> Distr b) -> Distr b
                                    ~~ dist μ1 μ2 <= PMonad.l => true => 
                                            dist (r1 μ1 f1) (r2 μ2 f2) <= PMonad.l @-}

{-@ assume relational upd ~ upd :: x1:Int -> α1:Int -> Int ~ x2:Int -> α2:Int -> Int 
                                ~~ dist x1 x2 <= PMonad.l => α1 = α2 => dist (r1 x1 α1) (r2 x2 α2) <= PMonad.l @-}
upd :: Int -> Int -> Int
upd x α = x + α

foo :: [Int] -> Int -> Distr Int
foo []      x = ppure x
foo (α : a) x = pbind (ppure $ upd x α) (foo a)

{-@ relational foo ~ foo :: a1:[Int] -> x1:Int -> Distr Int ~ a2:[Int] -> x2:Int -> Distr Int 
                         ~~ a1 = a2 => 
                                dist x1 x2 <= PMonad.l => 
                                    dist (r1 a1 x1) (r2 a2 x2) <= PMonad.l @-}
