{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--betaequivalence"  @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts      #-}

module MonadMaybe where

import Prelude hiding (return, Maybe(..), (>>=))

import Proves
import Helper

-- | Monad Laws :
-- | Left identity:	  return a >>= f  ≡ f a
-- | Right identity:	m >>= return    ≡ m
-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ axiomatize return @-}
return :: a -> L a
return x = x ::: Emp

{-@ axiomatize bind @-}
bind :: L a -> (a -> L b) -> L b
bind m f
  | llen m > 0 = append (f (hd m)) (bind (tl m) f)
  | otherwise  = Emp


{-@ axiomatize append @-}
append :: L a -> L a -> L a
append xs ys
  | llen xs == 0 = ys
  | otherwise    = hd xs ::: append (tl xs) ys

-- | Left Identity
{-@ left_identity :: x:a -> f:(a -> L b) -> { bind (return x) f == f x } @-}
left_identity :: a -> (a -> L b) -> Proof
left_identity x f
  =   bind (return x) f
  ==. bind (x ::: Emp) f
  ==. append (f x) (bind Emp f)
  ==. append (f x) Emp
  ==. f x                      ? prop_append_neutral (f x)
  *** QED

-- | Right Identity

{-@ right_identity :: x:L a -> { bind x return == x } @-}
right_identity :: L a -> Proof
right_identity Emp
  = bind Emp return
  ==. Emp
  *** QED

right_identity (x ::: xs)
  =   bind (x ::: xs) return
  ==. append (return x)   (bind xs return)
  ==. append (x ::: Emp)    (bind xs return)
  ==. x ::: append Emp (bind xs return)
  ==. x ::: bind xs return
  ==. x ::: xs                              ? right_identity xs
  *** QED


-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)
{-@ associativity :: m:L a -> f: (a -> L b) -> g:(b -> L c)
  -> {bind (bind m f) g == bind m (\x:a -> (bind (f x) g)) } @-}
associativity :: L a -> (a -> L b) -> (b -> L c) -> Proof
associativity Emp f g
  =   bind (bind Emp f) g
  ==. bind Emp g
  ==. Emp
  ==. bind Emp (\x -> (bind (f x) g))
  *** QED
associativity (x ::: xs) f g
  =   bind (bind (x ::: xs) f) g
  ==. bind (append (f x) (bind xs f)) g                    ? bind_append (f x) (bind xs f) g
  ==. append (bind (f x) g) (bind (bind xs f) g)
  ==. append (bind (f x) g) (bind xs (\y -> bind (f y) g)) ? associativity xs f g
  ==. append ((\y -> bind (f y) g) x) (bind xs (\y -> bind (f y) g)) ? βequivalence f g x 
  ==. bind (x ::: xs) (\y -> bind (f y) g)
  *** QED



{-@ βequivalence :: f:(a -> L b) -> g:(b -> L c) -> x:a -> 
     {bind (f x) g == (\y:a -> bind (f y) g) (x)}  @-}
βequivalence :: (a -> L b) -> (b -> L c) -> a -> Proof
βequivalence f g x = simpleProof 

bind_append :: L a -> L a -> (a -> L b) -> Proof
{-@ bind_append :: xs:L a -> ys:L a -> f:(a -> L b)
     -> { bind (append xs ys) f == append (bind xs f) (bind ys f) }
  @-}

bind_append Emp ys f
  =   bind (append Emp ys) f
  ==. bind ys f
  ==. append Emp (bind ys f)
  ==. append (bind Emp f) (bind ys f)
  *** QED
bind_append (x ::: xs) ys f
  =   bind (append (x ::: xs) ys) f
  ==. bind (x ::: append xs ys) f
  ==. append (f x) (bind (append xs ys) f)
  ==. append (f x) (append (bind xs f) (bind ys f)) ? bind_append xs ys f
  ==. append (append (f x) (bind xs f)) (bind ys f) ? prop_assoc (f x) (bind xs f) (bind ys f)
  ==. append (bind (x ::: xs) f) (bind ys f)
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


-- NV TODO: import there

-- imported from Append
prop_append_neutral :: L a -> Proof
{-@ prop_append_neutral :: xs:L a -> { append xs Emp == xs }  @-}
prop_append_neutral Emp
  = append Emp Emp ==. Emp
  *** QED
prop_append_neutral (x ::: xs)
  =   append (x ::: xs) Emp
  ==. x ::: append xs Emp
  ==. x ::: xs             ? prop_append_neutral xs
  *** QED

{-@ prop_assoc :: xs:L a -> ys:L a -> zs:L a
               -> { append (append xs ys) zs == append xs (append ys zs) } @-}
prop_assoc :: L a -> L a -> L a -> Proof
prop_assoc Emp ys zs
  =   append (append Emp ys) zs
  ==. append ys zs
  ==. append Emp (append ys zs)
  *** QED

prop_assoc (x ::: xs) ys zs
  =   append (append (x ::: xs) ys) zs
  ==. append (x ::: append xs ys) zs
  ==. x ::: append (append xs ys) zs
  ==. x ::: append xs (append ys zs)  ? prop_assoc xs ys zs
  ==. append (x ::: xs) (append ys zs)
  *** QED
