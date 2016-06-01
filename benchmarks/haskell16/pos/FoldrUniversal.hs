-- | Universal property of foldr a la Zombie
-- | cite : http://www.seas.upenn.edu/~sweirich/papers/congruence-extended.pdf

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

module FoldrUniversal where

import Proves
import Prelude hiding (foldr)

-- | foldrUniversal
{-@ axiomatize foldr @-}
foldr :: (a -> b -> b) -> b -> L a -> b
foldr f b xs
  | llen xs > 0
  = f (hd xs) (foldr f b (tl xs))
  | otherwise
  = b


{-@ foldrUniversal
  :: f:(a -> b -> b)
  -> h:(L a -> b)
  -> e:b
  -> ys:L a
  -> base:{h Emp == e }
  -> ih  : (x:a -> xs:L a -> {h (C x xs) == f x (h xs)})
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
foldrUniversal f h e Emp base hi
  =   h Emp
  ==! e               -- ? base
  ==! foldr f e Emp
  *** QED
foldrUniversal f h e (C x xs) base ih
  =   h (C x xs)
  ==! f x (h xs)         ? ih x xs
  ==! f x (foldr f e xs) ? foldrUniversal f h e xs base ih
  ==! foldr f e (C x xs)
  *** QED

-- | foldrFunsion

{-@ foldrFusion :: h:(b -> c) -> f:(a -> b -> b) -> g:(a -> c -> c) -> e:b -> ys:L a
            -> p1:(x:a -> y:b -> {v:Proof | h (f x y) == g x (h y)})
            -> { (compose h (foldr f e)) (ys) == foldr g (h e) ys }
  @-}
foldrFusion :: (b -> c) -> (a -> b -> b) -> (a -> c -> c) -> b -> L a
             -> (a -> b -> Proof)
             -> Proof
foldrFusion h f g e ys thm
  = foldrUniversal g (compose h (foldr f e)) (h e) ys
       (prop_base h f e)
       (prop_ind h f e g thm)

prop_ind :: (b -> c) -> (a -> b -> b) -> b -> (a -> c -> c)
         -> (a -> b -> Proof)
         -> a -> L a -> Proof
{-@ prop_ind :: h:(b -> c) -> f:(a -> b -> b) -> e:b -> g:(a -> c -> c)
         -> thm:(x:a -> y:b -> {v:Proof | h (f x y) == g x (h y)})
         -> x:a -> xs:L a
         -> {(compose h (foldr f e)) (C x xs) == g x ((compose h (foldr f e)) (xs))}
  @-}
prop_ind h f e g thm x Emp
  =   (compose h (foldr f e)) (C x Emp)
  ==! h (foldr f e (C x Emp))
  ==! h (f x (foldr f e Emp))
  ==! h (f x e)
  ==! g x (h e)  ? thm x e
  ==! g x (h (foldr f e Emp))
  ==! g x ((compose h (foldr f e)) Emp)
  *** QED

prop_ind h f e g thm x (C y ys)
  =   (compose h (foldr f e)) (C x (C y ys))
  ==! h (foldr f e (C x (C y ys)))
  ==! h (f x (foldr f e (C y ys)))
  ==! h (f x (f y (foldr f e ys)))
  ==! g x (h (f y (foldr f e ys)))
        ? thm x (f y (foldr f e ys))
  ==! g x (h (foldr f e (C y ys)))
  ==! g x ((compose h (foldr f e)) (C y ys))
  *** QED

prop_base :: (b->c) -> (a -> b -> b) -> b -> Proof
{-@ prop_base :: h:(b->c) -> f:(a -> b -> b) -> e:b
              -> { (compose h (foldr f e)) (Emp) == h e } @-}
prop_base h f e
  =   (compose h (foldr f e)) Emp
  ==! h (foldr f e Emp)
  ==! h e
  *** QED



{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) ->  a -> c
compose f g x = f (g x)

data L a = Emp | C a (L a)
{-@ data L [llen] @-}


{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen Emp        = 0
llen (C _ xs) = 1 + llen xs

{-@ measure hd @-}
{-@ hd :: {v:L a | llen v > 0 } -> a @-}
hd :: L a -> a
hd (C x _) = x

{-@ measure tl @-}
{-@ tl :: xs:{L a | llen xs > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a
tl (C _ xs) = xs
