{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module ListFunctors where

import Prelude hiding (fmap, id, Maybe(..), seq, pure)

import Language.Haskell.Liquid.ProofCombinators

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u


{-@ data Maybe a = Nothing | Just a @-}
data Maybe a = Nothing | Just a

{-@ reflect pure @-}
pure :: a -> Maybe a
pure x = Just x

{-@ reflect seq @-}
seq :: Maybe (a -> b) -> Maybe a -> Maybe b
seq (Just f) (Just x) = Just (f x)
seq _         _       = Nothing

{-@ reflect fmap @-}
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap f (Just x) = Just (f x)
fmap f Nothing  = Nothing

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect idollar @-}
idollar :: a -> (a -> b) -> b
idollar x f = f x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)


-- | Identity

{-@ identity :: x:Maybe a -> { seq (pure id) x == x } @-}
identity :: Maybe a -> Proof
identity Nothing = trivial 
identity (Just _) = trivial 



-- | homomorphism  pure f <*> pure x = pure (f x)

{-@ homomorphism :: f:(a -> a) -> x:a
                 -> { seq (pure f) (pure x) == pure (f x) } @-}
homomorphism :: (a -> a) -> a -> Proof
homomorphism _ _ 
  = trivial




-- | interchange

interchange :: Maybe (a -> a) -> a -> Proof
{-@ interchange :: u:(Maybe (a -> a)) -> y:a
     -> { seq u (pure y) == seq (pure (idollar y)) u }
  @-}
interchange Nothing _
  = trivial
interchange (Just _) _
  = trivial

-- | Composition

{-@ composition :: x:Maybe (a -> a)
                -> y:Maybe (a -> a)
                -> z:Maybe a
                -> {seq (seq (seq (pure compose) x) y) z = seq x (seq y z) } @-}
composition :: Maybe (a -> a) -> Maybe (a -> a) -> Maybe a -> Proof
composition Nothing _ _ 
   = trivial 
composition _ Nothing _
   = trivial
composition _ _ Nothing
   = trivial
composition (Just _) (Just _) (Just _)
  = trivial


