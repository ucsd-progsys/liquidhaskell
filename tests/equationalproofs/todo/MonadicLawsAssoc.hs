
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
module Append where

import Axiomatize
import Equational
import Prelude hiding (return, (>>=))


data L a = N |  C a (L a)

-- | Definition of the list monad

{-@ axiomatize return @-}
$(axiomatize
  [d| return :: a -> L a
      return x = C x N
    |])


{-@ axiomatize append @-}
$(axiomatize
  [d| append :: L a -> L a -> L a
      append N ys        = ys
      append (C x xs) ys = C x (append xs ys)
    |])

{-@ axiomatize bind @-}
$(axiomatize
  [d| bind :: L a -> (a -> L a) -> L a
      bind N        f = N
      bind (C x xs) f = append (f x) (xs `bind` f)
    |])

-- | Left Associativity: (m >>= f) >>= g ≡  m >>= (\x -> f x >>= g)


helper :: Eq a => a -> L a -> (a -> L a) -> (a -> L a) -> Proof
{-@ helper ::  x:a -> xs:L a -> f:(a -> L a) -> g:(a -> L a) 
            ->   {v: Proof| bind (append (f x) (bind N f)) g == append (bind (f x) g) (bind (bind N f) g)} @-}
helper x xs f g 
--   = auto 2 (bind (append fx N) g == bind fx  g )
--     = refl (bind (append (f x) (bind N f)) g) `by` pr1 `by` pr2 `by` pr3 `by` pr4 `by` pr5 
     = auto 2 (bind (append (f x) N) g ==  bind (f x) g ) 
  where 
{- 
    e1  = bind (append (f x) (bind N f)) g
    pr1 = axiom_bind_N f 
    e2  = bind (append (f x) N) g
    pr2 = prop_app_nil (f x)
    e3  = bind (f x) g 
    pr3 = prop_app_nil (bind (f x)  g)
    e4  = append (bind (f x) g) N
    pr4 = axiom_bind_N f     
    e5  = append (bind (f x) g) (bind N f)
    pr5 = axiom_bind_N g   
    e6  = append (bind (f x) g) (bind (bind N f) g)

-}


helper x xs f g 
  = undefined -- auto 2 ((append (f x) (xs `bind` f)) `bind` g ==  append (f x `bind` g) ((xs `bind` f) `bind` g)) 


{-@ prop_app_nil :: ys:L a -> {v:Proof | append ys N == ys} @-}
prop_app_nil :: (Eq a) => L a -> Proof
prop_app_nil N        = auto 1 (append N N        == N     )
prop_app_nil (C x xs) = auto 1 (append (C x xs) N == C x xs)

prop_left_assoc :: Eq a => L a -> (a -> L a) -> (a -> L a) -> Proof
{-@ prop_left_assoc :: m: L a -> f:(a -> L a) -> g:(a -> L a) -> Proof @-}
prop_left_assoc N f g 
  = refl ((N `bind` f) `bind` g) `by` pr1 `by` pr2 `by` pr3 
  where
    e1  = (N `bind` f) `bind` g
    pr1 = axiom_bind_N f 
    e2  = N `bind` g
    pr2 = axiom_bind_N g
    e3  = N
    pr3 = axiom_bind_N ((\x -> f x `bind` g))
    e4  = N `bind` (\x -> f x `bind` g)


prop_left_assoc (C x xs) f g 
  = undefined -- refl ((C x xs `bind` f) `bind` g) 
  where
    e1  = (C x xs `bind` f) `bind` g

    e2 = (append (f x) (xs `bind` f)) `bind` g 




    ei =  append (f x `bind` g) ((xs `bind` f) `bind` g)
    ej =  append ((\x -> f x `bind` g) x) ((xs `bind` f) `bind` g)



    ek =  append ((\x -> f x `bind` g) x) (xs `bind` (\x -> f x `bind` g))
    en =  C x xs `bind` (\x -> f x `bind` g)

-- | List definition


instance Eq a => Eq (L a) where
  N == N                 = True
  (C x xs) == (C x' xs') = x == x' && xs == xs'

{-@ data L [llen] @-}
{-@ invariant {v: L a | llen v >= 0} @-}

{-@ measure llen @-}
llen :: L a -> Int
llen N = 0
llen (C x xs) = 1 + llen xs
