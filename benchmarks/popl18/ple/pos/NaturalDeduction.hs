-- Author Niki Vazou 
-- Natural Deduction Rules for Quantifiers
-- Proofs from http://hume.ucdavis.edu/mattey/phi112/112dedurles_ho.pdf
-- and file:///Users/niki/Downloads/Gentzen%201935%20-%20Investigations%20into%20Logical%20Deduction%20(1).pdf

module Examples where

{-@ LIQUID "--higherorder" @-}

import Language.Haskell.Liquid.ProofCombinators

-- Universal Introduction
{-@ 
ex1 :: f:(a -> Bool) -> g:(a -> Bool)
    -> (x:a -> PAnd {v:Proof | f x} {v:Proof | g x})
    -> (y:a -> {v:Proof | f y})
  @-}
ex1 :: (a -> Bool) -> (a -> Bool)
    -> (a -> PAnd Proof Proof)
    -> (a -> Proof)
ex1 f g assumption y = 
  case assumption y of 
    PAnd fy _ -> fy  


class NonEmpty a where
  pick :: a 

-- Existential Introduction

{-@ ex2 :: f:(a -> Bool) -> (x:a -> {v:Proof | f x})
      -> (y::a,{v:Proof | f y}) @-}
ex2 :: NonEmpty a => (a -> Bool) -> (a -> Proof) -> (a,Proof)
ex2 f fx = (y, fx y)
  where
    y = pick


-- Existential Elimination 
-- exists x. (f x && g x)
-- => 
-- exists x. f x && exists x. g x 
{-@ existsAllDistr :: f:(a -> Bool) -> g:(a -> Bool) -> (x::a, PAnd {v:Proof | f x} {v:Proof | g x})
      -> PAnd (x::a, {v:Proof | f x}) (x::a, {v:Proof | g x}) @-}
existsAllDistr :: (a -> Bool) -> (a -> Bool) -> (a,PAnd Proof Proof) -> PAnd (a,Proof) (a,Proof)
existsAllDistr f g (x,PAnd fx gx) = PAnd (x,fx) (x,gx)

-- exists x. (f x || g x)
-- => 
-- (exists x. f x) || (exists x. g x)
{-@ existsOrDistr :: f:(a -> Bool) -> g:(a -> Bool) -> (x::a, POr {v:Proof | f x} {v:Proof | g x})
      -> POr (x::a, {v:Proof | f x}) (x::a, {v:Proof | g x}) @-}
existsOrDistr :: (a -> Bool) -> (a -> Bool) -> (a,POr Proof Proof) -> POr (a,Proof) (a,Proof)
existsOrDistr f g (x,POrLeft fx)  = POrLeft  (x,fx) 
existsOrDistr f g (x,POrRight fx) = POrRight (x,fx) 


-- forall x. (f x && g x)
-- => 
-- (forall x. f x && forall x g x)
{-@ forallAndDistr :: f:(a -> Bool) -> g:(a -> Bool) -> (x:a -> PAnd {v:Proof | f x} {v:Proof | g x})
      -> PAnd (x:a -> {v:Proof | f x}) (x:a -> {v:Proof | g x}) @-}
forallAndDistr :: (a -> Bool) -> (a -> Bool) -> (a -> PAnd Proof Proof) -> PAnd (a -> Proof) (a -> Proof)
forallAndDistr f g andx 
  = PAnd (\x -> case andx x of PAnd fx _ -> fx)
         (\x -> case andx x of PAnd _ gx -> gx)


-- forall x. (exists y. (p x => q x y)) 
-- => 
-- forall x. (p x => exists y. q x y)
{-@ forallExistsImpl :: p:(a -> Bool) -> q:(a -> a -> Bool)
      -> (x:a -> (y::a, {v:Proof | p x} -> {v:Proof | q x y} ))
      -> (x:a -> ({v:Proof | p x} -> (y::a, {v:Proof | q x y})))@-}
forallExistsImpl :: (a -> Bool) -> (a -> a -> Bool)
  -> (a -> (a,Proof -> Proof))
  -> (a -> (Proof -> (a,Proof)))
forallExistsImpl p q f x px 
  = case f x of 
      (y, pxToqxy) -> (y,pxToqxy px)

-- Gentze examples 

gentze1 :: Bool -> Bool -> Bool -> Proof
{-@ gentze1 :: x:Bool -> y:Bool -> z:Bool -> { (x || (y && z)) => ((x || y) && (x || z)) } @-}
gentze1 _ _ _ = ()


gentze2 :: (a -> a -> Bool) -> (a,a -> Proof) -> a -> (a,Proof)
{-@ gentze2 :: f:(a -> a -> Bool) -> (x::a,y:a -> {v:Proof | f x y}) -> y:a -> (x::a,{v:Proof | f x y}) @-}
gentze2 f (x,fxy) y = (x,fxy y)

gentze3 :: (a -> Bool) -> ((a, Proof)-> Proof) -> a -> Proof -> Proof
{-@ gentze3 :: f:(a -> Bool) -> ((x::a, {v:Proof | f x})-> {v:Proof | false}) 
            -> y:a -> {v:Proof | f y} -> {v:Proof | false} @-}
gentze3 f notexistsfx y fy = 
    notexistsfx (y, fy)


data POr  a b = POrLeft a | POrRight b 
data PAnd a b = PAnd a b 


