{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--eliminate" @-}
{-@ LIQUID "--maxparams=10"  @-}
{-@ LIQUID "--higherorderqs" @-}



{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module ListFunctors where

import Prelude hiding (fmap, id, Maybe(..), seq, pure)

import Proves
import Helper

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u

{-@ axiomatize idollar @-}
idollar :: a -> (a -> b) -> b
idollar x f = f x


-- | interchange

interchange :: Maybe (a -> a) -> a -> Proof
{-@ interchange :: u:(Maybe (a -> a)) -> y:a
                -> {v:Proof | true }
  @-}
--   -> {v:Proof | seq u (pure y) == seq (pure (idollar y)) u }
interchange Nothing y
  = undefined
interchange (Just ffff) y
  = toProof $
               (from_Just (Just ffff)) y
           ==! ffff y
           ==! idollar y ffff


data Maybe a = Nothing | Just a

{-@ measure from_Just @-}
from_Just :: Maybe a -> a
{-@ from_Just :: xs:{Maybe a | true } -> {v:a  | v == from_Just xs}@-}
from_Just (Just x) = x
