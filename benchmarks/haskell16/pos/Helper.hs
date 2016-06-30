
-- | Proving ackermann properties from
-- | http://www.cs.yorku.ca/~gt/papers/Ackermann-function.pdf

{-@ LIQUID "--higherorder"   @-}
{-@ LIQUID "--autoproofs"    @-}
{-@ LIQUID "--totality"      @-}


module Helper (

    gen_increasing, gen_increasing2

  , gen_incr

  , lambda_expand
  ) where

import Proves


lambda_expand :: Arg r => (r -> a) -> Proof 
{-@ lambda_expand :: r:(r -> a) -> { (\x:r -> r x) == r } @-}
lambda_expand r 
  = ( r =*=! \x -> r x) (body_lambda_expand r) *** QED 


body_lambda_expand :: Arg r => (r -> a) -> r -> Proof 
{-@ body_lambda_expand :: r:(r -> a) -> y:r -> { (\x:r -> r x) (y)  == r y } @-}
body_lambda_expand r y = simpleProof 



-- | forall f :: a -> a
-- |   if    forall x:Nat.   f x < f (x+1)
-- |   then  forall x,y:Nat.  x < y => f x < f y

{-@ type Greater N = {v:Int | N < v } @-}

gen_increasing :: (Int -> Int) -> (Int -> Proof) -> (Int -> Int -> Proof)
{-@ gen_increasing :: f:(Nat -> Int)
                   -> (z:Nat -> {v:Proof | f z < f (z+1) })
                   ->  x:Nat -> y:Greater x -> {v:Proof | f x < f y } / [y] @-}
gen_increasing f thm x y

  | x + 1 == y
  = f y ==! f (x + 1)
         >! f x       ?  thm x
        *** QED

  | x + 1 < y
  = f x
  <!  f (y-1)   ?   gen_increasing f thm x (y-1)
  <!  f y       ?   thm (y-1)
  *** QED
revgen_increasing :: (Int -> Int) -> (Int -> Int -> Proof) -> (Int -> Proof)
{-@ revgen_increasing :: f:(Nat -> Int)
                   ->  (x:Nat -> y:Greater x -> {v:Proof | f x < f y })
                   -> z:Nat -> {v:Proof | f z < f (z+1) } @-}
revgen_increasing f thm z
  = thm z (z+1)

gen_incr :: (Int -> Int) -> (Int -> Proof) -> (Int -> Int -> Proof)
{-@ gen_incr :: f:(Nat -> Int)
                   -> (z:Nat -> {f z <= f (z+1)})
                   ->  x:Nat -> y:Greater x -> {f x <= f y} / [y] @-}
gen_incr f thm x y

  | x + 1 == y
  = f x <=! f (x + 1) ? thm x
        <=! f y
        *** QED

  | x + 1 < y
  = f x  <=! f (y-1)   ?   gen_incr f thm x (y-1)
         <=! f y       ?   thm (y-1)
         *** QED


gen_increasing2 :: (Int -> a -> Int) -> (a -> Int -> Proof) -> (a -> Int -> Int -> Proof)
{-@ gen_increasing2 :: f:(Nat -> a -> Int)
                    -> (w:a -> z:Nat -> {v:Proof | f z w < f (z+1) w })
                    ->  c:a -> x:Nat -> y:Greater x -> {v:Proof | f x c < f y c } / [y] @-}
gen_increasing2 f thm c x y
  | x + 1 == y
  = f y c ==! f (x + 1) c
           >! f x c        ? thm c x
          *** QED

  | x + 1 < y
  = f x c <!  f (y-1) c    ? gen_increasing2 f thm c x (y-1)
          <!  f y c        ? thm c (y-1)
          *** QED
