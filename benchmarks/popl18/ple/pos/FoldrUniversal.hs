-- | Universal property of foldr a la Zombie
-- | cite : http://www.seas.upenn.edu/~sweirich/papers/congruence-extended.pdf

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"     @-}

module FoldrUniversal where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (foldr)

-- | foldrUniversal
{-@ axiomatize foldr @-}
foldr :: (a -> b -> b) -> b -> L a -> b
foldr f b (C x xs) = f x (foldr f b xs)
foldr f b Emp      = b


{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) ->  a -> c
compose f g x = f (g x)

{-@ foldrUniversal
      :: f:(a -> b -> b)
      -> h:(L a -> b)
      -> e:b
      -> ys:L a
      -> base:{h Emp == e }
      -> step: (x:a -> xs:L a -> {h (C x xs) == f x (h xs)})
      -> { h ys == foldr f e ys }
  @-}
foldrUniversal
    :: (a -> b -> b)
    -> (L a -> b)
    -> b
    -> L a
    -> Proof
    -> (a -> L a -> Proof)
    -> Proof
foldrUniversal f h e Emp base step
  =   trivial
foldrUniversal f h e (C x xs) base step
  =   step x xs &&& foldrUniversal f h e xs base step


-- | foldrFunsion

{-@ foldrFusion :: h:(b -> c) -> f:(a -> b -> b) -> g:(a -> c -> c) -> e:b -> ys:L a
            -> fuse:(x:a -> y:b -> {h (f x y) == g x (h y)})
            -> { (compose h (foldr f e)) (ys) == foldr g (h e) ys }
  @-}
foldrFusion :: (b -> c) -> (a -> b -> b) -> (a -> c -> c) -> b -> L a
             -> (a -> b -> Proof)
             -> Proof
foldrFusion h f g e ys fuse
  = foldrUniversal g (compose h (foldr f e)) (h e) ys
       (fuse_base h f e)
       (fuse_step h f e g fuse)

fuse_step :: (b -> c) -> (a -> b -> b) -> b -> (a -> c -> c)
         -> (a -> b -> Proof)
         -> a -> L a -> Proof
{-@ fuse_step :: h:(b -> c) -> f:(a -> b -> b) -> e:b -> g:(a -> c -> c)
         -> thm:(x:a -> y:b -> { h (f x y) == g x (h y)})
         -> x:a -> xs:L a
         -> {(compose h (foldr f e)) (C x xs) == g x ((compose h (foldr f e)) (xs))}
  @-}
fuse_step h f e g thm x Emp
  = thm x e

fuse_step h f e g thm x (C y ys)
  = thm x (f y (foldr f e ys))

fuse_base :: (b->c) -> (a -> b -> b) -> b -> Proof
{-@ fuse_base :: h:(b->c) -> f:(a -> b -> b) -> e:b
              -> { compose h (foldr f e) Emp == h e } @-}
fuse_base h f e
  = trivial



data L a = Emp | C a (L a)
{-@ data L [llen] a = Emp | C {hs :: a, tl :: L a} @-}


{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen Emp        = 0
llen (C _ xs) = 1 + llen xs
