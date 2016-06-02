{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorderqs" @-}

module MonoidList where

import Prelude hiding (mappend, mempty)

import Proves

-- | Monoid
-- | mempty-left ∀ x . mappend mempty  x ≡ x
-- | mempty-right ∀ x . mappend x  mempty ≡ x
-- | mappend-assoc ∀ x y z . mappend (mappend x  y) z ≡ mappend x (mappend y z)

{-@ axiomatize mappend @-}
mappend :: L a -> L a -> L a
mappend xs ys
  | llen xs == 0 = ys
  | otherwise    = hd xs ::: mappend (tl xs) ys

{-@ axiomatize mempty @-}
mempty :: L a
mempty = Emp

mempty_left :: L a -> Proof
{-@ mempty_left :: x:L a -> {mappend mempty x == x}  @-}
mempty_left xs
  =   mappend mempty xs
  ==! mappend Emp xs
  ==! xs
  *** QED

mempty_right :: L a -> Proof
{-@ mempty_right :: x:L a -> {mappend x mempty == x}  @-}
mempty_right Emp
  = mappend Emp mempty ==! Emp
  *** QED

mempty_right (x ::: xs)
  =   mappend (x ::: xs) mempty
  ==! mappend (x:::xs) Emp
  ==! x ::: (mappend xs Emp)
  ==! x ::: xs             ? mempty_right xs
  *** QED

{-@ mappend_assoc :: xs:L a -> ys:L a -> zs:L a
               -> {mappend (mappend xs ys) zs == mappend xs (mappend ys zs) } @-}
mappend_assoc :: L a -> L a -> L a -> Proof
mappend_assoc Emp ys zs
  =   mappend (mappend Emp ys) zs
  ==! mappend ys zs
  ==! mappend Emp (mappend ys zs)
  *** QED

mappend_assoc (x ::: xs) ys zs
  =   mappend (mappend (x ::: xs) ys) zs
  ==! mappend (x ::: mappend xs ys) zs
  ==! x ::: mappend (mappend xs ys) zs
  ==! x ::: mappend xs (mappend ys zs)  ? mappend_assoc xs ys zs
  ==! mappend (x ::: xs) (mappend ys zs)
  *** QED

data L a = Emp | a ::: L a
{-@ data L [llen] @-}


{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen Emp        = 0
llen (_ ::: xs) = 1 + llen xs

{-@ measure hd @-}
{-@ hd :: {v:L a | llen v > 0 } -> a @-}
hd :: L a -> a
hd (x ::: _) = x

{-@ measure tl @-}
{-@ tl :: xs:{L a | llen xs > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a
tl (_ ::: xs) = xs
