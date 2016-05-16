
-- | Proving ackermann properties from
-- | http://www.cs.yorku.ca/~gt/papers/Ackermann-function.pdf

{-@ LIQUID "--higherorder"   @-}
{-@ LIQUID "--autoproofs"    @-}
{-@ LIQUID "--totality"      @-}
{-@ LIQUID "--maxparams=10"  @-}
{-@ LIQUID "--higherorderqs" @-}
{-@ LIQUID "--eliminate"     @-}


module Helper (

    gen_increasing, gen_increasing2

  , gen_increasing_eq

  , abstract

  ) where

import Proves

-- | Function abstractio: Can I prove this?

{-@ assume abstract :: f:(a -> b) -> g:(a -> b) -> (x:a -> {v:Proof | f x == g x })
             -> {v:Proof | f == g } @-}
abstract :: (a -> b) -> (a -> b) -> (a -> Proof) -> Proof
abstract _ _ _ = simpleProof




-- | forall f :: a -> a
-- |   if    forall x:Nat.   f x < f (x+1)
-- |   then  forall x,y:Nat.  x < y => f x < f y


gen_increasing :: (Int -> Int) -> (Int -> Proof) -> (Int -> Int -> Proof)
{-@ gen_increasing :: f:(Nat -> Int)
                   -> (z:Nat -> {v:Proof | f z < f (z+1) })
                   ->  x:Nat -> y:{Nat | x < y } -> {v:Proof | f x < f y } / [y] @-}
gen_increasing f thm x y

  | x + 1 == y
  = proof $
      f y ==! f (x + 1)
           >! f x       ?  thm x

  | x + 1 < y
  = proof $
      f x  <! f (y-1)   ?   gen_increasing f thm x (y-1)
           <! f y       ?   thm (y-1)


gen_increasing_eq :: (Int -> Int) -> (Int -> Proof) -> (Int -> Int -> Proof)
{-@ gen_increasing_eq :: f:(Nat -> Int)
                   -> (z:Nat -> {v:Proof | f z <= f (z+1) })
                   ->  x:Nat -> y:{Nat | x < y } -> {v:Proof | f x <= f y } / [y] @-}
gen_increasing_eq f thm x y

  | x + 1 == y
  = proof $
      f y ==! f (x + 1)
          >=! f x       ?  thm x

  | x + 1 < y
  = proof $
      f x  <=! f (y-1)   ?   gen_increasing_eq f thm x (y-1)
           <=! f y       ?   thm (y-1)


gen_increasing2 :: (Int -> a -> Int) -> (a -> Int -> Proof) -> (a -> Int -> Int -> Proof)
{-@ gen_increasing2 :: f:(Nat -> a -> Int)
                    -> (w:a -> z:Nat -> {v:Proof | f z w < f (z+1) w })
                    ->  c:a -> x:Nat -> y:{Nat | x < y } -> {v:Proof | f x c < f y c } / [y] @-}
gen_increasing2 f thm c x y
  | x + 1 == y
  = proof $
      f y c ==! f (x + 1) c
             >! f x c        ? thm c x

  | x + 1 < y
  = proof $
      f x c <! f (y-1) c    ? gen_increasing2 f thm c x (y-1)
            <! f y c        ? thm c (y-1)
