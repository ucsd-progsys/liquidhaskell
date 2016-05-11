{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--eliminate" @-}
{-@ LIQUID "--maxparams=10"  @-}
{-@ LIQUID "--higherorderqs" @-}



{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module ListFunctors where

import Prelude hiding (fmap, id, seq, pure)

import Proves
import Helper

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u


{-@ axiomatize pure @-}
pure :: a -> L a
pure x = C x N

{-@ axiomatize seq @-}
seq :: L (a -> b) -> L a -> L b
seq fs xs
  | llen fs > 0 = append (fmap (hd fs) xs) (seq (tl fs) xs)
  | otherwise   = N

{-@ axiomatize append @-}
append :: L a -> L a -> L a
append xs ys
  | llen xs == 0 = ys
  | otherwise    = C (hd xs) (append (tl xs) ys)

{-@ axiomatize fmap @-}
fmap :: (a -> b) -> L a -> L b
fmap f xs
  | llen xs == 0 = N
  | otherwise    = C (f (hd xs)) (fmap f (tl xs))

{-@ axiomatize id @-}
id :: a -> a
id x = x

{-@ axiomatize idollar @-}
idollar :: a -> (a -> b) -> b
idollar x f = f x

{-@ axiomatize compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)


-- | Identity
{-
{- identity :: x:L a -> {v:Proof | seq (pure id) x == x } @-}
identity :: L a -> Proof
identity xs
  = toProof $
       seq (pure id) xs
         ==! seq (C id N) xs
         ==! append (fmap id xs) (seq N xs)
         ==! append xs N                     ? fmap_id xs
         ==! xs                              ? prop_append_neutral xs


-- | Composition

{- composition :: x:L (a -> a)
                -> y:L (a -> a)
                -> z:L a
                -> {v:Proof | (seq (seq (seq (pure compose) x) y) z) == seq x (seq y z) } @-}
composition :: L (a -> a) -> L (a -> a) -> L a -> Proof
composition xss@(C x xs) yss@(C y ys) zss@(C z zs)
   = undefined
{-
     toProof $
        seq (seq (seq (pure compose) xss) yss) zss
         ==! seq (seq (seq (C compose N) xss) yss) zss
         ==! seq (seq (append (fmap compose xss) (seq N xss)) yss) zss
         ==! seq (seq (append (fmap compose xss) N) yss) zss
         ==! seq (seq (fmap compose xss) yss) zss ? prop_append_neutral (fmap compose xss)
         ==! seq (seq (fmap compose (C x xs)) yss) zss
         ==! seq (seq (C (compose x) (fmap compose xs)) yss) zss
         ==! seq (append (fmap (compose x) yss) (seq (fmap compose xs) yss)) zss
         ==! seq (append (fmap (compose x) (C y ys)) (seq (fmap compose xs) yss)) zss
         ==! seq (append (C (compose x y) (fmap (compose x) ys)) (seq (fmap compose xs) yss)) zss
         ==! seq (C (compose x y) (append (fmap (compose x) ys) (seq (fmap compose xs) yss))) zss
         ==! append (fmap (compose x y) zss) (seq (append (fmap (compose x) ys) (seq (fmap compose xs) yss)) zss)
         ==! append (fmap (compose x y) (C z zs)) (seq (append (fmap (compose x) ys) (seq (fmap compose xs) yss)) zss)
         ==! C (compose x y z) (append (fmap (compose x y) zs) (seq (append (fmap (compose x) ys) (seq (fmap compose xs) yss)) zss))
-}
composition _ _ _
   = undefined

-- | homomorphism  pure f <*> pure x = pure (f x)

{- homomorphism :: f:(a -> a) -> x:a
                 -> {v:Proof | seq (pure f) (pure x) == pure (f x) } @-}
homomorphism :: (a -> a) -> a -> Proof
homomorphism f x
  = undefined


-- | interchange

interchange :: L (a -> a) -> a -> Proof
{- interchange :: u:(L (a -> a)) -> y:a
     -> {v:Proof | seq u (pure y) == seq (pure (idollar y)) u }
  @-}
interchange N y
  = undefined
interchange (C x xs) y
  = undefined
-}

data L a = N | C a (L a)
{-@ data L [llen] @-}

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen N        = 0
llen (C _ xs) = 1 + llen xs

{-@ measure hd @-}
{-@ hd :: {v:L a | llen v > 0 } -> a @-}
hd :: L a -> a
hd (C x _) = x

{-@ measure tl @-}
{-@ tl :: xs:{L a | llen xs > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a
tl (C _ xs) = xs



-- | TODO: Cuurently I cannot improve proofs
-- | HERE I duplicate the code...
-- | FunctorList
{-@ fmap_id :: xs:L a -> {v:Proof | fmap id xs == id xs } @-}
fmap_id :: L a -> Proof
fmap_id N
  = toProof $
      fmap id N ==! N
                ==! id N
fmap_id (C x xs)
  = toProof $
      fmap id (C x xs) ==! C (id x) (fmap id xs)
                       ==! C x (fmap id xs)
                       ==! C x (id xs)            ? fmap_id xs
                       ==! C x xs
                       ==! id (C x xs)

-- imported from Append
prop_append_neutral :: L a -> Proof
{-@ prop_append_neutral :: xs:L a -> {v:Proof | append xs N == xs }  @-}
prop_append_neutral N
  = toProof $
       append N N ==! N
prop_append_neutral (C x xs)
  = toProof $
       append (C x xs) N ==! C x (append xs N)
                         ==! C x xs             ? prop_append_neutral xs
