-- ISSUE: In the below datatype, mickeymouse is clearly UNBOUND, and yet
-- LH happily chugs along, and just says UNSAT at the end, instead of
-- pointing out the bogus datatype definition.

module TODOUnboundAbsRef () where

import Language.Haskell.Liquid.Prelude

{-@ LIQUID "--no-termination" @-}


{-@
data List [llen] a <p :: x0:a -> x1:a -> Bool>
  = Nil
  | Cons { lHd :: a, lTl :: List <p> (a <p mickeymouse>) }
@-}

{-@ measure llen :: (List a) -> Int
    llen(Nil)       = 0
    llen(Cons x xs) = 1 + (llen xs)
  @-}

{-@ invariant {v:(List a) | ((llen v) >= 0)} @-}

data List a = Nil | Cons a (List a)

{-
low, high :: Int
low  = 0
high = 10
-}

range l h =
  if l <= h then Cons l (range (l+1) h) else Nil

chk y =
  case y of
   Nil -> True
   Cons x1 xs -> case xs of
                 Nil -> True
                 Cons x2 xs2 -> liquidAssertB (x1 <= x2) && chk xs2

prop3 = chk $ range 1 100
