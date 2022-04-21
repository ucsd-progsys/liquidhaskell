{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{- LIQUID "--betaequivalence"  @-}	

module MonadList where

import Prelude hiding (return, (>>=))

import Language.Haskell.Liquid.ProofCombinators


-- | Monad Laws :
-- | Left identity:	  return a >>= f  ≡ f a
-- | Right identity:	m >>= return    ≡ m
-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ reflect return @-}
return :: a -> L a
return x = C x Emp

{-@ reflect bind @-}
bind :: L a -> (a -> L b) -> L b
bind Emp f = Emp
bind (C x xs) f = append (f x) (bind xs f)


{-@ reflect append @-}
append :: L a -> L a -> L a
append Emp ys = ys 
append (C x xs) ys = C x (append xs ys)

-- | Left Identity
{-@ left_identity :: x:a -> f:(a -> L b) -> { bind (return x) f == f x } @-}
left_identity :: a -> (a -> L b) -> Proof
left_identity x f
  =  prop_append_neutral (f x)


-- | Right Identity

{-@ right_identity :: x:L a -> { bind x return == x } @-}
right_identity :: L a -> Proof
right_identity Emp
  = trivial  

right_identity (C x xs)
  = right_identity xs


-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ assume associativity :: m:L a -> f: (a -> L b) -> g:(b -> L c)
      -> {bind (bind m f) g == bind m (\x:a -> (bind (f x) g)) } @-}
associativity :: L a -> (a -> L b) -> (b -> L c) -> Proof
associativity Emp f g
  = trivial 

associativity (C x xs) f g
  =   bind_append (f x) (bind xs f) g
  &&& associativity xs f g


bind_append :: L a -> L a -> (a -> L b) -> Proof
{-@ bind_append :: xs:L a -> ys:L a -> f:(a -> L b)
     -> { bind (append xs ys) f == append (bind xs f) (bind ys f) }
  @-}

bind_append Emp ys f
  =  trivial 
bind_append (C x  xs) ys f
  =   bind_append xs ys f
  &&& prop_assoc (f x) (bind xs f) (bind ys f)

{-@ data L [llen] @-} 
data L a = Emp | C a  (L a)

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen Emp        = 0
llen (C _ xs) = 1 + llen xs


-- NV TODO: import there

-- imported from Append
prop_append_neutral :: L a -> Proof
{-@ assume prop_append_neutral :: xs:L a -> { append xs Emp == xs }  @-}
prop_append_neutral Emp 
  = trivial 
prop_append_neutral (C x xs)
  = prop_append_neutral xs

{-@ assume prop_assoc :: xs:L a -> ys:L a -> zs:L a
               -> { append (append xs ys) zs == append xs (append ys zs) } @-}
prop_assoc :: L a -> L a -> L a -> Proof
prop_assoc Emp ys zs
  =  trivial 

prop_assoc (C x xs) ys zs
  =   prop_assoc xs ys zs

