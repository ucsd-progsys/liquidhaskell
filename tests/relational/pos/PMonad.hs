{-@ LIQUID "--no-totality" @-}
module PMonad where

import           Prelude                 hiding ( all
                                                , elem
                                                , sum
                                                )
import           Data.Functor.Identity

type Distr a = Identity a

{-@ measure PMonad.l :: Double @-}

{-@ measure PMonad.lq :: Double @-}

{-@ measure PMonad.lp :: Double @-}

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
                                    ~~ dist μ1 μ2 <= PMonad.lp => 
                                        (dist x1 x2 <= PMonad.lp => dist (r1 x1) (r2 x2) <= PMonad.l) =>
                                            dist (r1 μ1 f1) (r2 μ2 f2) <= PMonad.l @-}

qbind :: Distr a -> (a -> Distr b) -> Distr b
qbind = undefined

{-@ assume relational qbind ~ qbind :: μ1:Distr a -> f1:(x1:a -> Distr b) -> Distr b 
                                     ~ μ2:Distr a -> f2:(x2:a -> Distr b) -> Distr b
                                    ~~ dist μ1 μ2 <= PMonad.lq => 
                                        (dist x1 x2 <= PMonad.lq => dist (r1 x1) (r2 x2) <= PMonad.l) => 
                                            dist (r1 μ1 f1) (r2 μ2 f2) <= PMonad.l @-}

{-

<> Psi x1 x2 = Psi (getId x1) (getId x2)

       a1 ~ a2 | Phi r1 r2
________________________________
unit a1 ~ unit a2 | <> Phi r1 r2

                    a1 ~ a2 | q
                    a1 ~ a2 | <> Phi r1 r2
f1 ~ f2 | forall x1 x2. Phi x1 x2 => <> Psi (r1 x1) (r2 x2)
___________________________________________________________
             bind a1 f1 ~ bind a2 f2 | <> Psi r1 r2


                    a1 ~ a2 | <> Phi r1 r2
Phi x1 x2 |- f1 ~ f2 | <> Psi (r1 x1) (r2 x2)
___________________________________________________________
             bind a1 f1 ~ bind a2 f2 | <> Psi r1 r2

-}

{- assume relational pbind ~ pbind :: μ1:Distr a -> f1:(x1:a -> Distr b) -> Distr b 
                                     ~ μ2:Distr a -> f2:(x2:a -> Distr b) -> Distr b
                                    ~~ phi (getId μ1) (getId μ2) => 
                                        (x1 = x2 => psi (getId (f1 x1)) (getId (f2 x2))) => 
                                            psi (getId (r1 μ1 f1)) (getId (r1 μ1 f1)) @-}

{- assume relational pbind ~ pbind :: μ1:Distr a -> f1:(x1:a -> Distr b) -> Distr b 
                                     ~ μ2:Distr a -> f2:(x2:a -> Distr b) -> Distr b
                                    ~~ phi (getId μ1) (getId μ2) => 
                                        (true => psi (getId (f1 x1)) (getId (f2 x2))) => 
                                            psi (getId (r1 μ1 f1)) (getId (r1 μ1 f1)) @-}

{- 
idInt :: Int -> Int
idBool :: Bool -> Bool

id :: a -> a

let id x = x in (idInt 1, idBool True)
-}

{-@ assume relational upd ~ upd :: x1:Int -> α1:Bool -> Int ~ x2:Int -> α2:Bool -> Int 
                                ~~ dist x1 x2 <= PMonad.l => α1 = α2 => dist (r1 x1 α1) (r2 x2 α2) <= PMonad.lp @-}


{-@ assume relational upd ~ upd :: x1:Int -> α1:Bool -> Int ~ x2:Int -> α2:Bool -> Int 
                                ~~ dist x1 x2 <= PMonad.l => α1 /= α2 => dist (r1 x1 α1) (r2 x2 α2) <= PMonad.lq @-}
upd :: Int -> Bool -> Int
upd _ _ = undefined

-- {-@ measure b :: Bool @-}
-- b :: Bool
-- b = undefined

foo :: [Bool] -> Int -> Distr Int
foo _       x = ppure x
foo (α : a) x = if α then pbind (ppure (upd x α)) (foo a) else qbind (ppure (upd x α)) (foo a)

{-@ reflect all @-}
{-@ all :: xs:[Bool] -> Bool @-}
all :: [Bool] -> Bool   
all [] = True
all (x:xs) = x && all xs
 
{-@ relational foo ~ foo :: a1:[Bool] -> x1:Int -> Distr Int ~ a2:[Bool] -> x2:Int -> Distr Int 
                         ~~ PMonad.all a1 => 
                                dist x1 x2 <= PMonad.l => 
                                    dist (r1 a1 x1) (r2 a2 x2) <= PMonad.l @-}
