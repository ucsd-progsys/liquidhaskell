{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}



module MonadId where

import Prelude hiding (return, (>>=))

import Language.Haskell.Liquid.ProofCombinators
-- import Helper

-- | Monad Laws :
-- | Left identity:	  return a >>= f  ≡ f a
-- | Right identity:	m >>= return    ≡ m
-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ reflect return @-}
return :: a -> Identity a
return x = Identity x

{-@ reflect bind @-}
bind :: Identity a -> (a -> Identity b) -> Identity b
bind (Identity x) f = f x

data Identity a = Identity a

-- | Left Identity
{-@ left_identity :: x:a -> f:(a -> Identity b) -> { bind (return x) f == f x } @-}
left_identity :: a -> (a -> Identity b) -> Proof
left_identity x f
  =   trivial 

-- | Right Identity

{-@ right_identity :: x:Identity a -> { bind x return == x } @-}
right_identity :: Identity a -> Proof
right_identity (Identity x)
  =   trivial 

-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ associativity :: m:Identity a -> f: (a -> Identity b) -> g:(b -> Identity c)
      -> {bind (bind m f) g == bind m (\x:a -> (bind (f x) g)) } @-}
associativity :: Identity a -> (a -> Identity b) -> (b -> Identity c) -> Proof
associativity (Identity x) f g
  =   beta_reduce x f g 

beta_reduce :: a -> (a -> Identity b) -> (b -> Identity c) -> Proof 
{-@ assume beta_reduce :: x:a -> f:(a -> Identity b) -> g:(b -> Identity c)
                -> {bind (f x) g == (\y:a -> bind (f y) g) (x)}  @-}
beta_reduce x f g = trivial 

 
