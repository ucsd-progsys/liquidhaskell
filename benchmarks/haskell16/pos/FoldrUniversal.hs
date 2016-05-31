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
  -> {v:Proof | h ys == foldr f e ys }
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
