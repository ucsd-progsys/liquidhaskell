{-# OPTIONS_GHC -Wno-missing-methods #-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--no-totality" @-}

module T1708 where

import Language.Haskell.Liquid.ProofCombinators


bool1, bool2 :: Bool
bool1 = undefined
bool2 = undefined

class Eq a => EqAdequate a where
  toSMT :: a -> a -> PBEq a -> ()

{-@ class Eq a => EqAdequate a where
      toSMT :: x:a -> y:a -> PEq a {x} {y} -> {x = y} 
  @-}

instance EqAdequate Bool where

data PBEq a
{-@ measure eqT :: a -> a -> Bool @-}
{-@ type PEq a E1 E2 = {v:PBEq a | eqT E1 E2} @-}
{-@ cEq  :: x:a -> y:a -> PEq a {x} {y} -> ctx:(a -> b) -> PEq b {ctx x} {ctx y} @-}
cEq  :: a -> a -> PBEq a -> (a -> b) -> PBEq b
cEq = undefined

{-@ critical :: {x:a | slowSpec x } -> a @-}
critical :: a -> a
critical x = x

{-@ bar :: PEq (a -> Bool) {fastSpec} {slowSpec} -> a -> Maybe a @-}
bar :: PBEq (a -> Bool) -> a -> Maybe a
bar pf x = if fastSpec x ? toSMT (fastSpec x) (slowSpec x) (unExt fastSpec slowSpec  pf x)
            then Just (critical x)
            else Nothing

{-@ unExt :: f:(a -> b) -> g:(a -> b) -> PEq (a -> b) {f} {g} -> x:a -> PEq b {f x} {g x} @-}
unExt :: (a -> b) -> (a -> b) -> PBEq (a -> b) -> a -> PBEq b
unExt f g p x = cEq f g p (flip' x) ? flip' x f ? flip' x g

{-@ reflect flip' @-}
flip' :: a -> (a -> b) -> b
flip' x f = f x

{-@ reflect fastSpec @-}
fastSpec :: a -> Bool
fastSpec _ = bool1

{-@ reflect slowSpec @-}
slowSpec :: a -> Bool
slowSpec _ = bool2
